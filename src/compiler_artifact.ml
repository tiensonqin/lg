let magic = "LG-COMPILER-STATE"
let version = 49
let maximum_payload_bytes = 512 * 1024 * 1024

let remove_if_present path =
  try if Sys.file_exists path then Sys.remove path with Sys_error _ -> ()

let copy_channel input_channel output_channel =
  let buffer = Bytes.create 65536 in
  let rec loop () =
    match input input_channel buffer 0 (Bytes.length buffer) with
    | 0 -> ()
    | count ->
        output output_channel buffer 0 count;
        loop ()
  in
  loop ()

let write ~kind ~path value =
  let directory = Filename.dirname path in
  let payload_path = Filename.temp_file ~temp_dir:directory "payload-" ".tmp" in
  let artifact_path =
    Filename.temp_file ~temp_dir:directory "artifact-" ".tmp"
  in
  try
    let payload_output = open_out_bin payload_path in
    Fun.protect
      ~finally:(fun () -> close_out_noerr payload_output)
      (fun () -> Marshal.to_channel payload_output value []);
    let payload_length = (Unix.stat payload_path).st_size in
    let payload_digest = Digest.file payload_path |> Digest.to_hex in
    let payload_input = open_in_bin payload_path in
    let artifact_output = open_out_bin artifact_path in
    Fun.protect
      ~finally:(fun () ->
        close_in_noerr payload_input;
        close_out_noerr artifact_output)
      (fun () ->
        Printf.fprintf artifact_output "%s\n%d\n%s\n%d\n%s\n" magic version
          kind payload_length payload_digest;
        copy_channel payload_input artifact_output);
    Sys.rename artifact_path path;
    remove_if_present payload_path
  with exn ->
    remove_if_present payload_path;
    remove_if_present artifact_path;
    raise exn

let read ~kind ~path =
  let truncated () = Error "truncated compiler state artifact" in
  try
    let input_channel = open_in_bin path in
    Fun.protect
      ~finally:(fun () -> close_in_noerr input_channel)
      (fun () ->
        let required_line () =
          try Some (input_line input_channel) with End_of_file -> None
        in
        match required_line () with
        | None -> truncated ()
        | Some actual_magic when not (String.equal actual_magic magic) ->
            Error "invalid compiler state artifact"
        | Some _ -> (
            match required_line () with
            | None -> truncated ()
            | Some version_text -> (
                match int_of_string_opt version_text with
                | None -> Error "invalid compiler state artifact version"
                | Some actual_version when actual_version <> version ->
                    Error
                      (Printf.sprintf "unsupported compiler state version %d"
                         actual_version)
                | Some _ -> (
                    match (required_line (), required_line (), required_line ()) with
                    | Some actual_kind, Some length_text, Some expected_digest
                      when String.equal actual_kind kind -> (
                        match int_of_string_opt length_text with
                        | None -> Error "invalid compiler state artifact length"
                        | Some payload_length when payload_length < 0 ->
                            Error "invalid compiler state artifact length"
                        | Some payload_length
                          when payload_length > maximum_payload_bytes ->
                            Error "compiler state artifact exceeds maximum size"
                        | Some payload_length ->
                            let payload_start = pos_in input_channel in
                            let remaining =
                              in_channel_length input_channel - payload_start
                            in
                            if remaining < payload_length then truncated ()
                            else if remaining > payload_length then
                              Error "invalid compiler state artifact trailing data"
                            else
                              let actual_digest =
                                Digest.channel input_channel payload_length
                                |> Digest.to_hex
                              in
                              if not (String.equal actual_digest expected_digest)
                              then Error "compiler state artifact checksum mismatch"
                              else (
                                seek_in input_channel payload_start;
                                try Ok (Marshal.from_channel input_channel)
                                with _ ->
                                  Error "invalid compiler state artifact payload"))
                    | Some _, Some _, Some _ ->
                        Error "invalid compiler state artifact kind"
                    | _ -> truncated ()))))
  with Sys_error message ->
    Error ("invalid compiler state artifact: " ^ message)
