## The Document Manager

### internal

Some internal modules are actually not private in the `dune` sense, since we
also generate binaries which do need to see these modules.

- [scheduler](scheduler.mli) is in charge of analyzing a document and plan
  its execution. It knows which Coq sentences change the parser and which
  sentences bracket a proof. A schedule is built incrementally, as sentences
  are discovered. The component holds a notion of dependency among sentences
  which is used to invalidate upon change.

- [parTactic](parTactic.mli) implements the `par:` combinator based on SEL.

- [delegationManager](delegationManager.mli) implements an OS agnostic way to
  delegate a job to a worker process.

- [executionManager](executionManager.mli) holds the Coq state associated to
  sentences which it can execute based on a schedule and potentially delegating
  some work via the delegation manager.

- [document](document.mli) holds the text as seen by the user and its validated
  (parsed) form. Since parsing and execution are entangled in Coq, validation
  stops at the first sentence which has a parsing effect.

### public

- [documentManager](documentManager.mli) is the main entry point for user
  actions, like interpret_to_position.

