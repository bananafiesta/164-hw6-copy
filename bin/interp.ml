open Core
open Lib

let command =
  Command.basic ~summary:"Interpret the given file"
    Command.Let_syntax.(
      let%map_open filename = anon (maybe ("filename" %: Command.Param.string))
      and expression =
        flag "-e" (optional string) ~doc:"expression to evaluate"
      in
      fun () ->
        try
          match (filename, expression) with
          | Some f, _ ->
              S_exp.parse_file_many f |> Interp.interp ;
              print_endline ""
          | _, Some e ->
              S_exp.parse_many e |> Interp.interp ;
              print_endline ""
          | _ ->
              Printf.eprintf
                "Error: must specify either an expression to evaluate or a file\n"
        with e -> Printf.eprintf "Error: %s\n" (Exn.to_string e))

let () = Command_unix.run ~version:"1.0" command
