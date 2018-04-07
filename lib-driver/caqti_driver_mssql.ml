(* Copyright (C) 2017--2018  Petter A. Urkedal <paurkedal@gmail.com>
 *
 * This library is free software; you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or (at your
 * option) any later version, with the OCaml static compilation exception.
 *
 * This library is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public
 * License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this library.  If not, see <http://www.gnu.org/licenses/>.
*)

open Caqti_driver_lib
open Caqti_prereq
open Printf
open Freetds

(* FIXME: Need to catch Dblib.Error pretty much everywhere we call Dblib
   functions, and also need to make all Dblib functions use their own thread,
   not a random helper thread. *)

type Caqti_error.msg += Mssql_msg of Dblib.severity * int * string
let () =
  let pp ppf = function
    | Mssql_msg (_severity, code, msg) ->
      Format.fprintf ppf "Error %d, %s" code msg
    | _ -> assert false in
  Caqti_error.define_msg ~pp [%extension_constructor Mssql_msg]

module Connect_functor (System : Caqti_system_sig.S) = struct
  open System

  let (>>|) m f = m >>= fun r -> return (f r)
  let (>>=?) m mf = m >>= (function Ok x -> mf x | Error _ as r -> return r)

  module type CONNECTION =
    Caqti_connection_sig.Base with type 'a future := 'a System.future

  let driver_info =
    Caqti_driver_info.create
      ~uri_scheme:"mssql"
      ~dialect_tag:`Mssql
      ~parameter_style:`None
      ~can_pool:true
      ~can_concur:true
      ~can_transact:true
      ~describe_has_typed_params:false (* TODO *)
      ~describe_has_typed_fields:false (* TODO *)
      ()

  module Connection (Db : sig val uri : Uri.t val db : Dblib.dbprocess end) : CONNECTION =
  struct
    open Db
    module StringMap = Map.Make(String)
    module Response = struct
      type ('b, +'m) t = {
        query: string;
        row_type: 'b Caqti_type.t;
      }

      let reject ~query msg =
        Error (Caqti_error.response_rejected ~uri ~query (Caqti_error.Msg msg))

      let reject_f ~query fmt =
        ksprintf (reject ~query) fmt

      let affected_count _ =
        Preemptive.detach (fun () -> Ok (Dblib.count db)) ()

      let returned_count t = affected_count t

      let exec { query } =
        Preemptive.detach (fun () ->
            if not (Dblib.results db) then
              reject_f ~query "No result set returned for exec."
            else Ok ()) ()

      let rec decode_field
        : type b. uri: Uri.t -> b Caqti_type.field ->
        Dblib.data -> (b, _) result =
        fun ~uri field_type field ->
          let open Dblib in
          try match field_type with
            | Caqti_type.Bool ->
              (match field with
               | BIT v -> Ok v
               | _ -> assert false)
            | Caqti_type.Int ->
              (match field with
               | INT v -> Ok v
               | _ -> assert false)
            | Caqti_type.Int32 ->
              (match field with
               | INT32 v -> Ok v
               | _ -> assert false)
            | Caqti_type.Int64 ->
              (match field with
               | INT64 v -> Ok (Int64.of_string v)
               | _ -> assert false)
            | Caqti_type.Float ->
              (match field with
               | FLOAT v -> Ok v
               | _ -> assert false)
            | Caqti_type.String ->
              (match field with
               | STRING v -> Ok v
               | _ -> assert false)
            | Caqti_type.Octets ->
              (match field with
               | BINARY v -> Ok v
               | _ -> assert false)
            (* TODO: This is surprisingly complicated because we can't trust
               FreeTDS's time zone:
               http://www.pymssql.org/en/stable/freetds_and_dates.html *)
            | Caqti_type.Pdate -> assert false
            | Caqti_type.Ptime -> assert false
            | Caqti_type.Ptime_span -> assert false
            | field_type ->
              (match Caqti_type.Field.coding driver_info field_type with
               | None -> Error (Caqti_error.decode_missing ~uri ~field_type ())
               | Some (Caqti_type.Field.Coding {rep; decode; _}) ->
                 (match decode_field ~uri rep field with
                  | Ok y ->
                    (match decode y with
                     | Ok _ as r -> r
                     | Error msg ->
                       let msg = Caqti_error.Msg msg in
                       let typ = Caqti_type.field field_type in
                       Error (Caqti_error.decode_rejected ~uri ~typ msg))
                  | Error _ as r -> r))
          with
          | Failure _ ->
            (* TODO: Better error message using column type etc. *)
            let msg = Caqti_error.Msg ("Convert failed.") in
            let typ = Caqti_type.field field_type in
            Error (Caqti_error.decode_rejected ~uri ~typ msg)

      let rec decode_row
        : type b. uri: Uri.t -> Dblib.data array -> int -> b Caqti_type.t ->
        (int * b, _) result =
        fun ~uri row i ->
          function
          | Caqti_type.Unit -> Ok (i, ())
          | Caqti_type.Field ft ->
            (match decode_field ~uri ft row.(i) with
             | Ok fv -> Ok (i + 1, fv)
             | Error _ as r -> r)
          | Caqti_type.Option t ->
            let j = i + Caqti_type.length t in
            let rec null_only k =
              k = j || row.(k) = Dblib.NULL && null_only (i + 1) in
            if null_only i then Ok (j, None) else
              (match decode_row ~uri row i t with
               | Ok (j, y) -> Ok (j, Some y)
               | Error _ as r -> r)
          | Caqti_type.Tup2 (t0, t1) ->
            decode_row ~uri row i t0 |>? fun (i, y0) ->
            decode_row ~uri row i t1 |>? fun (i, y1) ->
            Ok (i, (y0, y1))
          | Caqti_type.Tup3 (t0, t1, t2) ->
            decode_row ~uri row i t0 |>? fun (i, y0) ->
            decode_row ~uri row i t1 |>? fun (i, y1) ->
            decode_row ~uri row i t2 |>? fun (i, y2) ->
            Ok (i, (y0, y1, y2))
          | Caqti_type.Tup4 (t0, t1, t2, t3) ->
            decode_row ~uri row i t0 |>? fun (i, y0) ->
            decode_row ~uri row i t1 |>? fun (i, y1) ->
            decode_row ~uri row i t2 |>? fun (i, y2) ->
            decode_row ~uri row i t3 |>? fun (i, y3) ->
            Ok (i, (y0, y1, y2, y3))
          | Caqti_type.Custom {rep; decode; _} as typ ->
            (match decode_row ~uri row i rep with
             | Ok (j, y) ->
               (match decode y with
                | Ok z -> Ok (j, z)
                | Error msg ->
                  let msg = Caqti_error.Msg msg in
                  Error (Caqti_error.decode_rejected ~uri ~typ msg))
             | Error _ as r -> r)

      let decode_next_row ~query conn row_type =
        try
          let row = Dblib.nextrow conn |> Array.of_list in
          match decode_row ~uri row 0 row_type with
          | Ok (_, row) -> Ok (Some row)
          | Error _ as e -> e
        with Not_found ->
          Ok None

      let find { query ; row_type } =
        (* TODO: Catch multiple rows returned in find *)
        Preemptive.detach (fun () ->
            match decode_next_row ~query db row_type with
            | Ok (Some row) -> Ok row
            | Ok None -> reject_f ~query "Received no tuples for find."
            | Error _ as e -> e) ()

      let find_opt { query ; row_type } =
        (* TODO: Catch multiple rows returned in find *)
        Preemptive.detach (fun () ->
            decode_next_row ~query db row_type) ()

      let fold f { query ; row_type } =
        let rec loop acc =
          Preemptive.detach (fun () -> decode_next_row ~query db row_type) ()
          >>= function
          | Ok None -> return (Ok acc)
          | Ok (Some y) -> loop (f y acc)
          | Error _ as r -> return r
        in
        loop

      let fold_s f { query ; row_type } =
        let rec loop acc =
          Preemptive.detach (fun () -> decode_next_row ~query db row_type) ()
          >>= function
          | Ok None -> return (Ok acc)
          | Ok (Some y) -> f y acc >>=? loop
          | Error _ as r -> return r
        in
        loop

      let iter_s f { query ; row_type } =
        let rec loop () =
          Preemptive.detach (fun () -> decode_next_row ~query db row_type) ()
          >>= function
          | Ok None -> return (Ok ())
          | Ok (Some y) -> f y >>=? loop
          | Error _ as r -> return r
        in
        loop ()
    end

    let validate () = return true (* FIXME *)
    let check f = f true (* FIXME *)

    let call ~f req _param =
      let row_type = Caqti_request.row_type req in
      let templ = Caqti_request.query req driver_info in
      let query = linear_query_string templ in
      Preemptive.detach (fun() ->
          Dblib.sqlexec db query) ()
      >>= fun () ->
      f { Response.query ; row_type }

    let exec q = call ~f:Response.exec q ()
    let start () = exec (Caqti_request.exec Caqti_type.unit "BEGIN")
    let commit () = exec (Caqti_request.exec Caqti_type.unit "COMMIT")
    let rollback () = exec (Caqti_request.exec Caqti_type.unit "ROLLBACK")

    let disconnect () =
      Preemptive.detach (fun () ->
          Dblib.close db) ()
  end

  let connect uri =
    match Uri.scheme uri with
    | Some "mssql" ->
      let host = Uri.host uri in
      let user = Uri.user uri in
      let password = Uri.password uri in
      (match host, user, password with
       | Some host, Some user, Some password ->
         (* TODO: Custom port -- doesn't seem to be supported by ocaml-freetds *)
         (match Uri.path uri with
          | "/" -> Ok None
          | path ->
            if Filename.dirname path <> "/" then
              let msg = Caqti_error.Msg "Bad URI path." in
              Error (Caqti_error.connect_rejected ~uri msg)
            else
              Ok (Some (Filename.basename path)))
         |> return
         >>=? fun database ->
         Preemptive.detach (fun () ->
             let db = Dblib.connect ~charset:"UTF-8" ~user ~password host in
             Option.iter (Dblib.use db) database;
             let module Arg = struct let uri = uri let db = db end in
             let module Db = Connection (Arg) in
             Ok (module Db : CONNECTION)) ()
       | _ ->
         let missing =
           [ host, "host"
           ; user, "user"
           ; password, "password" ]
           |> List.filter (function
               | None, name -> true
               | _ -> false)
           |> List.map snd
           |> String.concat ", "
         in
         return (Error (Caqti_error.connect_rejected ~uri
                          (Caqti_error.Msg
                             (sprintf "Missing required parameter(s): \
                                       %s" missing)))))
    | _ ->
      return (Error (Caqti_error.connect_rejected ~uri
                       (Caqti_error.Msg "URI doesn't not start with mssql://")))
end

let () = Caqti_connect.define_driver "mssql" (module Connect_functor)
