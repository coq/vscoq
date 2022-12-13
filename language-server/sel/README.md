## SEL : Simple Event Library

This library is the result of our experience in using threads and the Lwt async
monad to tame the problem of writing a server which has to listen and react to
multiple sources of events.

The problem comes from the fact that reading from an event source is blocking.

### Threads

Threads help you with that because you can have multiple threads, one per event
source. Our experience with OCaml threads is that their scheduling is not fair,
so one thread doing some computations can prevent the others from advancing.
Calling sleep here and there to recover fairness was sad. We also faced
a few bugs, some solved by now, where a thread would not wake up even if some
data was available in  its event source. Threads are nice since the context in
which a thread is paused is saved for you, you can suspend in the middle of a
complex piece of code very easily, actually it's transparent, you have to do
nothing to be suspended (at least in theory, barring an unfair scheduler).
OCaml threads do not run in parallel as of now. Moreover our target
application, Coq, has a lot of global state, so threads can anyway only be used
to deal with blocking reads, not to gain much performance. Or at least, not
without doing a lot of work.
Threads are part of OCaml's standard distribution, no external dependency.

### Lwt

The Lwt monad forces you to chop your code in thunks, continuations, you pass
to a quite extensive API taking care of scheduling and calling continuations
when the data is actually ready. Nice syntax comes at the price of the PPX stack
which is not a little dependency, or at least OCaml 4.08 where `let*` like
syntax is available. Monads are "viral", you have to push the monad all over
the place if you want to take advantage of of Lwt. Lwt is also a bit viral,
it wants to take over many things behind the scenes. For example we had troubles
using `fork`. Reasoning about Lwt is supposed to be simple, but soon it is not.
Yes, you can predict when things run, but then you start to have detached
promises and some of the "randomness" threads have appears again.
Lwt looks amazing, but after a while it makes you wonder if the
French expression "usine à gaz" does not apply. It is well maintained, but it
is an external dependency with C code you may not want to maintain yourself if
things go south. After a while our code started to use less and less Lwt
features, at some point we even dropped promises. What was left was a loop
around a single wait, hence SEL.

### SEL

SEL is the old boring loop around `Unix.select`. Yes, it is not trendy.

The bad point is that you have to "reify" the state around the interruptible
points of computation. With threads it's the OS that does it for you saving the
stack. With Lwt you write a thunk, a closure, which is not very different.
With SEL you craft an ADT of the events and the constructors have to carry all
you need in order to handle that event. Event handlers can generate new events,
which are put in the pool of events which are eventually ready to be handled
later on.

```ocaml
  let rec loop evs =
    let ready, waiting = Sel.wait evs in
    let new_evs_l = List.map handle_event ready in
    loop (waiting @ List.concat new_evs_l)
```

Like a monad, the types force you to thread the list of new events back to
`Sel.wait` but there is no other "viral" effect.

Dispatching is not automatic, it's your `handle_event` that does it.

```ocaml
  type event =
    | NotForMe of OtherComponent.event
    | Echo of string
    | EchoError

  let echo : event Sel.event =
    Sel.on_line Unix.stdin (function
    | Ok s -> Echo s
    | Error _ -> EchoError)

  let handle_event = function
    | NotForMe e -> OtherComponent.handle_event e |>
        List.map (Sel.map (fun x -> NotForMe x))
    | Echo text ->
        Printf.printf "echo: %s\n" text;
        [echo]
    | EchoError ->
        Printf.eprintf "oops\n";
        exit 1
```

In the example the current module is in charge of the `Echo` event, and passes
the ball to `OtherComponent` to handle its events. The `echo` value generates
an `Echo` event as soon as one line is readable from `Unix.stdin`. The `Echo`
constructor has to carry all the data that is needed in order to handle that
event, in this case it is just a string. Handling an event can schedule new
events for later, for example handling `Echo` schedules another identical event.

```ocaml
let main () =
  loop [echo; ...]
```

That is all, for the good and the bad. One has to write some boring code, like
injecting the events of the other component into the `NotForMe` event, so that
dispatching can pass the ball correctly.

SEL provides a few `Sel.on_*` APIs to create events on which one can wait.
For example the death of a process, or an HTTP Content-Length encoded request,
or some item in a Queue, or some marhaled OCaml value.
All these APIs take a function to inject the actual data that comes with the
event inside the appropriate ADT constructor representing the event ready to be
handled.

Blocking calls are not forced to go trough SEL. You can read and write freely
while handling an event. It is up to you to avoid long or blocking computations
and to preserve some fairness. You can artificially split a computation in
steps and pass the ball to the scheduler by creating event with `Sel.now`,
which `Sel.wait` will find to be immediately ready *together* with all the
other events that happen to be ready.

Really? Yes, it is not intriguing intellectually speaking, but you can get some
fairness (which you don't get via threads nor Lwt) and you can actually
*interrupt* one of these split computations since `Sel.wait` gives you *all* the
events that are ready, so if the user sends a stop request you can look if both
`Stop` and `ContinueSplitComputation` are in the `ready` list and take action.
Nor threads nor Lwt have a good story about cancellation, not to talk about
a `Sys.Break` exception being raise where you don't expect it.

SEL is just some sugar atop `Unix.select` and is a single `.ml` file with no C
code.
