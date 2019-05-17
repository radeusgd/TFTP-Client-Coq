open Unix
open Arg

let x = 2

let y = Printf.printf "test\n"; 2

let fail message = Printf.printf "%s\n" message; exit 1

type transfer_direction = Upload of string | Download of string

let parse_args () =
  let ip = ref "" in
  let port = ref 69 in
  let upload = ref "" in
  let download = ref "" in
  Arg.parse [("-ip", Arg.Set_string ip, "IP address of server to connect to"); ("-port", Arg.Set_int port, "port of the server"); ("-download", Arg.Set_string download, "filename to download"); ("-upload", Arg.Set_string upload, "filename to upload")] (fun anon -> Printf.printf "Unrecognized argument: %s\n" anon; exit 1) "Simple TFTP client in OCaml and Coq";
  if !ip = "" then fail "IP not specified";
  if !upload = "" && !download = "" then fail "Provide a filename to download or upload";
  if !upload <> "" && !download <> "" then fail "You can either choose download or upload but not both";
  if !upload != "" then (!ip, !port, Upload !upload)
  else (!ip, !port, Download !download)

let main () =
  Printf.printf "hello world\n";
  let (ip, port, transfer) = parse_args () in
  Printf.printf "Connecting to %s:%d\n" ip port
