(**************************************************************************)
(*                                                                        *)
(*                                 VSCoq                                  *)
(*                                                                        *)
(*                   Copyright INRIA and contributors                     *)
(*       (see version control and README file for authors & dates)        *)
(*                                                                        *)
(**************************************************************************)
(*                                                                        *)
(*   This file is distributed under the terms of the MIT License.         *)
(*   See LICENSE file.                                                    *)
(*                                                                        *)
(**************************************************************************)

type 'a res = ('a,exn) result

(* Events in progress *)
type _ in_progress =
  | Line : Bytes.t * Buffer.t -> string in_progress
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
type 'a system_event =
  | ReadInProgress of Unix.file_descr * 'a fcomp
  | WaitProcess of int * (Unix.process_status -> 'a)
let pp_system_event _ fmt = function
  | ReadInProgress(_,_) -> Stdlib.Format.fprintf fmt "ReadInProgress"
  | WaitProcess(pid,_) -> Stdlib.Format.fprintf fmt "WaitProcess %d" pid

type 'a queue_event =
  | WaitQueue1 : 'b Queue.t * ('b -> 'a) -> 'a queue_event
  | WaitQueue2 : 'b Queue.t * 'c Queue.t * ('b -> 'c -> 'a) -> 'a queue_event

let pp_queue_event _ fmt = function
  | WaitQueue1 _ -> Stdlib.Format.fprintf fmt "WaitQueue1"
  | WaitQueue2 _ -> Stdlib.Format.fprintf fmt "WaitQueue2"

type 'a task_event = 'a [@@deriving show]

type cancellation_handle = bool ref [@@deriving show]
let cancel x = x := true

type ('a,'b) with_attributes = {
  name : string option ;
  recurring : 'a;
  priority : int;
  it : 'b;
  cancelled : cancellation_handle;
}
[@@deriving show]

let cmp_priority { priority = t1; _} { priority = t2; _} = t1 - t2

let name name it = { it with name = Some name }
let make_recurring x = { x with recurring = true }
let set_priority priority x = { x with priority }
let is_recurring { recurring; _ } = recurring <> None
let uncancellable (e,_) = e
let cancellation_handle { cancelled; _ } = cancelled

let make_event it =
  let cancelled = ref false in
  { name = None; recurring = false; priority = 0; cancelled; it }, cancelled

type 'a event_ =
  | SystemEvent of 'a system_event
  | QueueEvent of 'a queue_event
  | Task of 'a task_event
type 'a event = (bool,'a event_) with_attributes

let map_system_event f = function
  | WaitProcess(pid,k) -> WaitProcess(pid, (fun x -> f (k x)))
  | ReadInProgress(fd,fcomp) -> ReadInProgress(fd,map_fcomp f fcomp)
  
let map_queue_event f = function
  | WaitQueue1(q1,k) -> WaitQueue1(q1,(fun x -> f (k x)))
  | WaitQueue2(q1,q2,k) -> WaitQueue2(q1,q2,(fun x y -> f (k x y)))

let map_task_event f x = f x

let map_with_attributes f { name; recurring; priority; cancelled; it } =
  { name; recurring; priority; cancelled; it = f it }

let map f = function
  | Task e -> Task (map_task_event f e)
  | SystemEvent e -> SystemEvent (map_system_event f e)
  | QueueEvent e -> QueueEvent(map_queue_event f e)

let map f e = map_with_attributes (map f) e

type ('a,'b) has_finished =
  | Yes of 'a
  | No  of 'b (* can make_event a step *)

let mkReadInProgress fd = function
  | FCons _ as f -> No (ReadInProgress(fd,f))
  | FNil x -> Yes x

let one_line () = Line (Bytes.make 1 '0', Buffer.create 40)
let bytes n ?(buff=Bytes.create n) () = Bytes(n,buff)

let on_line fd k : 'a event * cancellation_handle =
  make_event @@ SystemEvent (ReadInProgress(fd, one_line () -- finish_with k))

let on_bytes fd n k : 'a event * cancellation_handle =
  make_event @@ SystemEvent (ReadInProgress(fd, bytes n () -- finish_with k))

let now task : 'a event =
  make_event @@ Task task |> uncancellable

let on_death_of ~pid k : 'a event * cancellation_handle =
  make_event @@ SystemEvent (WaitProcess(pid,k))

let ocaml_value (k : 'a res -> 'b) : 'b fcomp =
  let (--?) x y = err k x y in
  bytes Marshal.header_size ()
  --? (fun buff -> let data_size = Marshal.data_size buff 0 in
  bytes data_size ~buff:(Bytes.extend buff 0 data_size) ()
  --? (fun buff -> let value = Marshal.from_bytes buff 0 in
  finish_with k (Ok value)))
;;

let on_ocaml_value fd k : 'a event * cancellation_handle =
  make_event @@ SystemEvent (ReadInProgress(fd, ocaml_value k))

let parse_content_length_or err k s =
  try
    let input = Scanf.Scanning.from_string (String.uppercase_ascii s) in
    Scanf.bscanf input "CONTENT-LENGTH: %d" k
  with
    (Scanf.Scan_failure _ | Failure _ | End_of_file | Invalid_argument _) as e ->
      err (Error e)

let httpcle (k : Bytes.t res -> 'b) : 'b fcomp  =
  let (--?) x y = err k x y in
  one_line ()
  --? (parse_content_length_or (finish_with k) (fun length ->
  one_line ()
  --? (fun _discard ->
  bytes length ()
  --? (fun buff ->
  finish_with k (Ok buff)))))

let on_httpcle fd k : 'a event * cancellation_handle =
  make_event @@ SystemEvent (ReadInProgress(fd, httpcle k))

let on_queue q1 k : 'a event * cancellation_handle =
  make_event @@ QueueEvent (WaitQueue1(q1,k))

let on_queues q1 q2 k : 'a event * cancellation_handle =
  make_event @@ QueueEvent (WaitQueue2(q1,q2,k))

let cons_recurring e l =
  match e.recurring with
  | None -> l
  | Some x -> { e with it = x } :: l

let rec pull_ready f yes no min_priority = function
  | [] -> List.rev yes, List.rev no, min_priority
  | { it; cancelled; _ } as e :: rest ->
      match f cancelled it with
      | Yes y -> pull_ready f ({ e with it = y } :: yes) (cons_recurring e no) (min min_priority e.priority) rest
      | No x  -> pull_ready f yes ({ e with it = x } :: no) min_priority rest 

let pull_ready f l = pull_ready f [] [] max_int l

let cast_to_recurring : (bool, 'a) with_attributes -> 'b -> ('b option, 'b) with_attributes =
  fun e it ->
  { it;
    recurring = if e.recurring then Some it else None;
    name = e.name;
    priority = e.priority;
    cancelled = e.cancelled;
  }
let cast_to_not_recurring : ('b, 'a) with_attributes -> ('c option, 'a) with_attributes =
  fun e ->
  { it = e.it;
    recurring = None;
    name = e.name;
    priority = e.priority;
    cancelled = e.cancelled;
  }
  
let rec partition_events sys queue task = function
  | [] -> List.rev sys, List.rev queue, List.rev task
  | { it = SystemEvent x; _ } as e :: rest -> partition_events    (cast_to_recurring e x :: sys) queue task rest
  | { it = QueueEvent x; _ } as e :: rest -> partition_events sys (cast_to_recurring e x :: queue) task rest
  | { it = Task x; _ } as e :: rest -> partition_events sys queue (cast_to_recurring e x :: task) rest

let partition_events l = partition_events [] [] [] l

let advance_queue _ = function
  | WaitQueue1(q1,_) as x when Queue.is_empty q1 ->  No x
  | WaitQueue1(q1,k) -> Yes(k (Queue.pop q1))
  | WaitQueue2(q1,q2,_) as x when Queue.is_empty q1 || Queue.is_empty q2 -> No x
  | WaitQueue2(q1,q2,k) -> Yes(k (Queue.pop q1) (Queue.pop q2))

let advance_system ~ready_fds _ = function
  | WaitProcess(pid,k) as x ->
      let rc, code = Unix.waitpid [Unix.WNOHANG] pid in
      if rc == 0 then No x
      else Yes (k code)
  | ReadInProgress(_, FNil _) -> assert false
  | ReadInProgress(fd,_) as x when not (List.mem fd ready_fds) -> No x
  | ReadInProgress(fd, FCons(Line (buff,acc) as line,rest)) -> begin try
      let n = Unix.read fd buff 0 1 in
      if n = 0 then begin
        Buffer.clear acc;
        mkReadInProgress fd (rest (Error End_of_file))
      end else
        let c = Bytes.get buff 0 in
        if c != '\n' then begin
          Buffer.add_char acc c; 
          mkReadInProgress fd (FCons(line,rest))
        end else begin
          let one_line = Buffer.contents acc in
          Buffer.clear acc;
          mkReadInProgress fd (rest (Ok one_line))
        end
      with Unix.Unix_error _ as e ->
        Buffer.clear acc;
        mkReadInProgress fd (rest (Error e))
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
let check_for_system_events l =
  let fds = map_filter (function { it = ReadInProgress(fd,_); _ } -> Some fd | _ -> None) l in
  let ready_fds, _, _ = Unix.select fds [] [] 0.0 in
  let ready, waiting, min_prio  = pull_ready (advance_system ~ready_fds) l in
  ready, waiting, min_prio

let check_for_queue_events l =
  pull_ready advance_queue l

let next_deadline delta = Unix.gettimeofday() +. delta

module Sorted : sig

  type 'a list
  type 'a list_ =
    | Nil
    | Cons of 'a * int * 'a list

  val look : 'a list -> 'a list_
  val cons : 'a -> int -> 'a list -> 'a list
  val cons_opt : ('a * int) option -> 'a list -> 'a list
  val nil : 'a list
  val length : 'a list -> int
  val filter : ('a -> bool) -> 'a list -> 'a list
  val for_all : ('a -> bool) -> 'a list -> bool
  val map_to_list : ('a -> 'b) -> 'a list -> 'b List.t
  val append : 'a list -> 'a list -> 'a list
  val concat3 : ('a -> int) -> 'a List.t -> 'a List.t -> 'a list -> 'a list
  val sort : ('a -> int) -> 'a List.t -> 'a list
  val min : 'a list -> int
  val pp_list : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit

end = struct
  module L = struct type 'a t = 'a list [@@deriving show] end

  type 'a list = ('a * int) L.t
  [@@deriving show]

  type 'a list_ =
    | Nil
    | Cons of 'a * int * ('a * int) L.t

  let nil = []

  let length = List.length

  let on_fst f = (); fun (x,_) -> f x

  let filter f l = List.filter (on_fst f) l

  let for_all f l = List.for_all (on_fst f) l

  let min = function [] -> max_int | (_,p) :: _ -> p

  let look = function
    | [] -> Nil
    | (x,p) :: xs -> Cons(x,p,xs)

  let rec cons x p = function
    | [] -> [x,p]
    | (_,q) :: _ as l when p < q -> (x,p) :: l
    | (y,q) :: l -> (y,q) :: cons x p l
  let cons_opt = function
    | Some(x,p) -> cons x p
    | None -> fun x -> x

  let map_to_list f l = List.map (on_fst f) l

  let cmp (_,p1) (_,p2) = p1 - p2

  let append l1 l2 = List.sort cmp (l1 @ l2)
    
  let add_prio f l = List.map (fun x -> x, f x) l

  let concat3 f l1 l2 l3 = List.sort cmp (add_prio f l1 @ add_prio f l2 @ l3)

  let sort f l = add_prio f l |> List.sort cmp

end

let priority_sort l = List.stable_sort cmp_priority l

type 'a todo = {
  system : ('a system_event option,'a system_event) with_attributes list;
  queue  : ('a queue_event option,'a queue_event)  with_attributes list;
  tasks  : ('a task_event option,'a task_event)   with_attributes Sorted.list;
  ready  : ('a option,'a) with_attributes Sorted.list;
}
[@@deriving show]
let empty = { system = []; queue = [] ; tasks = Sorted.nil; ready = Sorted.nil }

let prune_cancelled { system; queue; tasks; ready } =
  let not_cancelled { cancelled; _ } = !cancelled = false in
  let system = List.filter not_cancelled system in
  let queue  = List.filter not_cancelled queue in
  let tasks  = Sorted.filter not_cancelled tasks in
  let ready  = Sorted.filter not_cancelled ready in
  { system; queue; tasks; ready }


let size todo =
  let { system; queue; tasks; ready } = prune_cancelled todo in
  List.(length system + length queue + Sorted.length tasks + Sorted.length ready )

let nothing_left_to_do todo =
  let { system; queue; tasks; ready } = prune_cancelled todo in
  system = [] && queue = [] && tasks = Sorted.nil && ready = Sorted.nil

let only_recurring_events todo =
  let { system; queue; tasks; ready } = prune_cancelled todo in
  List.for_all is_recurring system &&
  List.for_all is_recurring queue &&
  Sorted.for_all is_recurring tasks &&
  ready = Sorted.nil

(* This is blocking wait (modulo a deadline). We check for system events
   (io, process death) or a queue (in case some thread puts a token there). *)
let rec wait_for_system_or_queue_events ~deadline (fds,sys) queue =
  if Unix.gettimeofday () > deadline then [], [], sys, queue, max_int
  else
    let ready_fds, _, _ = Unix.select fds [] [] 0.1 in
    let ready_sys, waiting_sys, min_prio_sys = pull_ready (advance_system ~ready_fds) sys in
    let ready_queue, waiting_queue, min_prio_queue = pull_ready advance_queue queue in
    if ready_sys <> [] || ready_queue <> [] then ready_sys, ready_queue, waiting_sys, waiting_queue, min min_prio_queue min_prio_sys
    else wait_for_system_or_queue_events ~deadline (fds,waiting_sys) queue

let wait_return_sorted (l1,l2,l3,todo) =
  priority_sort l1 |> List.map (fun x -> x.it),
  priority_sort l2 |> List.map (fun x -> x.it),
  l3 |> Sorted.map_to_list (fun x -> x.it),
  todo

let cons_recurring_sorted e p l =
  match e.recurring with
  | None -> l
  | Some x -> Sorted.cons { e with it = x } p l
  

let pull_ready_sorted min_prio l =
  match Sorted.look l with
  | Sorted.Nil -> None, Sorted.nil
  | Sorted.Cons(_,p,_) when min_prio <= p -> None, l
  | Sorted.Cons(x,p,l) -> Some(x,p), cons_recurring_sorted x p l

let wait ?(deadline=max_float) todo =
  let { system; queue; tasks; ready } as todo = prune_cancelled todo in
  if nothing_left_to_do todo then
    [], [], Sorted.nil, todo
  else
    let ready_sys, waiting_sys, min_prio_sys = check_for_system_events system in
    let ready_queue, waiting_queue, min_prio_queue = check_for_queue_events queue in
    if ready = Sorted.nil && tasks = Sorted.nil && ready_queue = [] && ready_sys = [] then
      let fds = map_filter (function { it = ReadInProgress(fd,_); _ } -> Some fd | _ -> None) waiting_sys in
      let ready_sys, ready_queue, waiting_sys, waiting_queue, _ =
        wait_for_system_or_queue_events ~deadline (fds,waiting_sys) waiting_queue in
      ready_sys, ready_queue, Sorted.nil,
      { system = waiting_sys; queue = waiting_queue; tasks = Sorted.nil; ready = Sorted.nil }
    else
      let min_prio = min min_prio_sys min_prio_queue in
      let min_prio = min min_prio (Sorted.min ready) in
      let ready_task, waiting_tasks = pull_ready_sorted min_prio tasks in
      ready_sys, ready_queue, Sorted.cons_opt ready_task ready,
      { system = waiting_sys; queue = waiting_queue; tasks = waiting_tasks; ready = Sorted.nil }


let pop_return (ready_sys,ready_queue,ready_task, todo) =
  let ready_sys = List.map cast_to_not_recurring ready_sys in
  let ready_queue = List.map cast_to_not_recurring ready_queue in
  let ready = Sorted.concat3 (fun x -> x.priority) ready_sys ready_queue ready_task in
  match Sorted.look ready with
  | Sorted.Cons(x,_,ready) -> Some x.it, { todo with ready }
  | Sorted.Nil -> None, todo

let pop l =
  match pop_return @@ wait l with
  | None, _ -> raise @@ Failure "nothing to pop"
  | Some x, t -> x, t
let pop_opt l = pop_return @@ wait l

let pop_timeout ~stop_after_being_idle_for:delta l = 
  let deadline = next_deadline delta in
  pop_return @@ wait ~deadline l

let wait_timeout ~stop_after_being_idle_for:delta l =
  let deadline = next_deadline delta in
  wait_return_sorted @@ wait ~deadline l

let wait l = wait_return_sorted @@ wait l

let enqueue { system; queue; tasks; ready } l =
  let new_sys, new_queue, new_tasks = partition_events l in
  { 
    system = system @ new_sys;
    queue = queue @ new_queue;
    tasks = Sorted.append tasks (Sorted.sort (fun x -> x.priority) new_tasks);
    ready;
  }
