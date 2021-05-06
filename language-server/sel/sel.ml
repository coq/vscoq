(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type 'a res = ('a,exn) result

(* Events in progress *)
type _ in_progress =
  | Line : char list -> string in_progress
  | Bytes : int * Bytes.t -> Bytes.t in_progress

(* Reified function composition *)
type _ fcomp =
  | FNil : 'a -> 'a fcomp
  | FCons : 'a in_progress * ('a res -> 'b fcomp) -> 'b fcomp

let rec map_fcomp f = function
  | FNil x -> FNil (f x)
  | FCons(pending,g) -> FCons(pending,(fun x -> map_fcomp f (g x)))

let finish_with (k : 'a res -> 'b) x = FNil(k x)
let (--) = fun x xs -> FCons(x,xs)
(* locally one does let (--?) x y = err k x y in  as a cons with error handling *)
let err : type a b c. (c res -> b) -> a in_progress -> (a -> b fcomp) -> b fcomp =
  fun k x xs ->
    let xs = function
      | Ok v -> xs v
      | Error e -> FNil(k (Error e)) in
    FCons(x,xs)

(* Read events can be composed of many read operations *)
type 'a event =
  | ReadInProgress of Unix.file_descr * 'a fcomp
  | WaitProcess of int * (Unix.process_status -> 'a)
  | WaitQueue1 : 'b Queue.t * ('b -> 'a) -> 'a event
  | WaitQueue2 : 'b Queue.t * 'c Queue.t * ('b -> 'c -> 'a) -> 'a event
  | Ready of 'a

let map f = function
  | Ready x -> Ready (f x)
  | WaitQueue1(q1,k) -> WaitQueue1(q1,(fun x -> f (k x)))
  | WaitQueue2(q1,q2,k) -> WaitQueue2(q1,q2,(fun x y -> f (k x y)))
  | WaitProcess(pid,k) -> WaitProcess(pid, (fun x -> f (k x)))
  | ReadInProgress(fd,fcomp) -> ReadInProgress(fd,map_fcomp f fcomp)

let mkReadInProgress fd = function
  | FNil x -> Ready x
  | f -> ReadInProgress(fd,f)

let one_line = Line []
let bytes n ?(buff=Bytes.create n) () = Bytes(n,buff)

let on_line fd k = ReadInProgress(fd, one_line -- finish_with k)
let on_bytes fd n k = ReadInProgress(fd, bytes n () -- finish_with k)
let now x = Ready x
let on_death_of ~pid k = WaitProcess(pid,k)

let ocaml_value (k : 'a res -> 'b) : 'b fcomp =
  let (--?) x y = err k x y in
  bytes Marshal.header_size ()
  --? (fun buff -> let data_size = Marshal.data_size buff 0 in
  bytes data_size ~buff:(Bytes.extend buff 0 data_size) ()
  --? (fun buff -> let value = Marshal.from_bytes buff 0 in
  finish_with k (Ok value)))
;;

let on_ocaml_value fd k = ReadInProgress(fd, ocaml_value k)

let parse_content_length_or err k s =
  try
    let input = Scanf.Scanning.from_string (String.uppercase_ascii s) in
    Scanf.bscanf input "CONTENT-LENGTH: %d" k
  with
    (Scanf.Scan_failure _ | Failure _ | End_of_file | Invalid_argument _) as e ->
      err (Error e)

let httpcle (k : Bytes.t res -> 'b) : 'b fcomp  =
  let (--?) x y = err k x y in
  one_line
  --? (parse_content_length_or (finish_with k) (fun length ->
  one_line
  --? (fun _discard ->
  bytes length ()
  --? (fun buff ->
  finish_with k (Ok buff)))))

let on_httpcle fd k = ReadInProgress(fd, httpcle k)

let on_queue q1 k = WaitQueue1(q1,k)
let on_queues q1 q2 k = WaitQueue2(q1,q2,k)

let advance ~ready_fds = function
  | Ready _ as x -> x
  | WaitQueue1(q1,_) as x when Queue.is_empty q1 -> x
  | WaitQueue1(q1,k) -> Ready(k (Queue.pop q1))
  | WaitQueue2(q1,q2,_) as x when Queue.is_empty q1 || Queue.is_empty q2 -> x
  | WaitQueue2(q1,q2,k) -> Ready(k (Queue.pop q1) (Queue.pop q2))
  | WaitProcess(pid,k) as x ->
      let rc, code = Unix.waitpid [Unix.WNOHANG] pid in
      if rc == 0 then x
      else Ready (k code)
  | ReadInProgress(_, FNil _) -> assert false
  | ReadInProgress(fd,_) as x when not (List.mem fd ready_fds) -> x
  | ReadInProgress(fd, FCons(Line acc,rest)) -> begin try
      let buff = Bytes.make 1 '0' in
      let n = Unix.read fd buff 0 1 in
      if n = 0 then
        mkReadInProgress fd (rest (Error End_of_file))
      else
        let c = Bytes.get buff 0 in
        if c != '\n' then
          mkReadInProgress fd (FCons(Line (c :: acc),rest))
        else
          let one_line = String.concat "" (List.rev_map (String.make 1) acc) in
          mkReadInProgress fd (rest (Ok one_line))
      with Unix.Unix_error _ as e -> mkReadInProgress fd (rest (Error e))
      end
  | ReadInProgress(fd,FCons(Bytes(n,buff),rest)) -> begin try
      let m = Unix.read fd buff (Bytes.length buff - n) n in
      if m = 0 then
        mkReadInProgress fd (rest (Error End_of_file))
      else
        if m != n then
          mkReadInProgress fd (FCons(Bytes(n-m,buff),rest))
        else
          mkReadInProgress fd (rest (Ok buff))
      with Unix.Unix_error _ as e -> mkReadInProgress fd (rest (Error e))
      end

let rec partition_map f = function
  | [] -> [], []
  | x :: xs ->
      match f x with
      | None ->
          let a, b = partition_map f xs in
          a, x :: b
      | Some x ->
          let a, b = partition_map f xs in
          x :: a, b

let rec map_filter f = function
  | [] -> []
  | x :: xs ->
      match f x with
      | None -> map_filter f xs
      | Some x -> x :: map_filter f xs

(* For fairness reasons, even if there are immediately ready events we
   give a shot to system events with 0 wait, otherwise we wait until a
   system event is ready. We never sleep forever, since process death events
   do not wakeup select: we anyway wake up 10 times per second *)
let rec wait_system_events ~return l =
  let time = match return with `ASAP -> 0.0 | `OnEvents -> 0.1 in
  let fds = map_filter (function ReadInProgress(fd,_) -> Some fd | _ -> None) l in
  let ready_fds, _, _ = Unix.select fds [] [] time in
  let l = List.map (advance ~ready_fds) l in
  let ready, waiting = partition_map (function Ready x -> Some x | _ -> None) l in
  if ready <> [] || return = `ASAP then ready, waiting
  else wait_system_events ~return waiting

let wait l =
  let l = List.map (advance ~ready_fds:[]) l in
  let ready, waiting = partition_map (function Ready x -> Some x | _ -> None) l in
  if ready = [] then wait_system_events ~return:`OnEvents waiting
  else
    let more_ready, waiting = wait_system_events ~return:`ASAP waiting in
    ready @ more_ready, waiting
