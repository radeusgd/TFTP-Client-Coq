open Unix
open Arg
open Random
open String
open Bytes
open List
open TFTP_Core

let str_to_list (s : string) : char list = []  (* FIXME *)
let list_to_str (l : char list) : string = ""  (* FIXME *)
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

let assign_random_TID () : int =
  (* skipping first ports as they tend to require root *)
  (* TODO ranges *)
  Random.int (65535 - 1025) + 1025

let create_udp_socket (tid : int) : file_descr =
  let udp_protocol_type = 17 in
  let recv_timeout = 3.0 in
  let fd = Unix.socket PF_INET SOCK_DGRAM udp_protocol_type in
  let addr = Unix.ADDR_INET (inet_addr_any, tid) in
  Unix.setsockopt_float fd Unix.SO_RCVTIMEO recv_timeout;
  Unix.bind fd addr;
  fd

type state = TODO of int
type message = bytes
type action = Send of message * int | Terminate
type event = Incoming of message * int | Timeout (* TODO should also provide IP? *) (*TODO add terminated event*)

(* TODO these two functions should call the Coq core *)
let initialize_connection (tid : int) (port : int) (transfer : transfer_direction) : action * state =
  let tr = match transfer with
    | Upload fname -> TFTP_Core.Coq_upload (str_to_list fname)
    | Download fname -> TFTP_Core.Coq_download (str_to_list fname)
  in
  let TFTP_Core.Coq_makeresult (coq_action, coq_state) = TFTP_Core.initialize tid port tr in
  let action = match coq_action with
    | Coq_send (msg, port) -> Send (list_to_str msg, port)
    | Coq_terminate -> Terminate in
  let state = match coq_state with
    | Coq_todo -> TODO 0 in
  (action, state)

(*TODO connect with Coq*)
let process_step (event :  event) (state : state) : action * state =
  let (TODO port) = state in
  match event with
  | Timeout -> (Terminate, state)
  | Incoming (msg, inc_port) -> (Send (msg, inc_port), state)

let max_packet_len = 600

let main =
  Random.self_init(); (* initialize randomness *)
  Printf.printf "hello world\n";
  let (ip, port, transfer) = parse_args() in
  let tid = assign_random_TID () in
  Printf.printf "Connecting to %s:%d, my tid is %d\n%!" ip port tid;
  let fd = create_udp_socket tid in
  let make_addr port = ADDR_INET ((inet_addr_of_string ip), port) in
  let rec loop (action, state) =
    match action with
    | Terminate -> Printf.printf "quitting\n"; exit 0
    | Send (msg, port) ->
      Printf.printf "sending '%s'\n%!" (Bytes.to_string msg);
      let toaddr = make_addr port in
      let sent = Unix.sendto fd msg 0 (Bytes.length msg) [] toaddr in
      Printf.printf "waiting for reply\n%!";
      let buf = Bytes.create max_packet_len in
      try
        let (recvd, ADDR_INET (fromip, fromport)) = Unix.recvfrom fd buf 0 max_packet_len [] in
        if recvd <= 0 then (* TODO this is not a timeout but terminated conn *)
          loop (process_step Timeout state)
        else
          (Printf.printf "received '%s'\n%!" (Bytes.to_string buf);
          loop (process_step (Incoming (Bytes.sub buf 0 recvd, fromport)) state))
      with Unix.Unix_error (Unix.EAGAIN, "recvfrom", _) -> loop (process_step Timeout state)
  in
  loop (initialize_connection tid port transfer)
