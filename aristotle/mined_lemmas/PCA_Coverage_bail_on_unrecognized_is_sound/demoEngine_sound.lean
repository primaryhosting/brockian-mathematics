import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# A formal model of a bail-on-unrecognized isolation engine

This file develops an abstract model of an *isolation engine*: a monitor that consumes a
trace of events, maintaining an internal state, and that is only able to *recognize*
(interpret) some of the events it may be presented with.  The design discipline under study
is **bail on unrecognized input**: whenever the engine meets an event it does not recognize,
it stops interpreting the trace and moves into a designated *bail* (quarantine / isolate)
state instead of guessing.

The model consists of:

* `PCA.Coverage.Engine`, packaging the partial transition function `step`, the bail
  transition `bail`, and the safety invariant `Safe`;
* `PCA.Coverage.Engine.run`, the actual behaviour of the engine (bail on unrecognized);
* `PCA.Coverage.Engine.runOpt`, the idealized behaviour on *covered* traces (fails on
  unrecognized input);
* `PCA.Coverage.Engine.Bails`, the predicate "this trace drives the engine into bail".

The two main results are:

* **Soundness** (`PCA.Coverage.bail_on_unrecognized_is_sound`): the safety invariant is
  preserved by every run, on *every* trace, including traces containing events outside the
  engine's coverage; moreover the bail policy is not lossy — on a fully covered trace the
  engine reproduces exactly the idealized semantics.
* **Completeness of the coverage model**
  (`PCA.Coverage.bails_iff_exists_unrecognized_prefix`): the engine bails on a trace *if and
  only if* the trace really does contain an unrecognized event, reached along the idealized
  semantics.  So bailing is triggered by exactly the situations the model says it is.
-/

namespace PCA.Coverage

/-- An abstract isolation engine over events `Event` and internal states `State`.

* `step s e = some s'` means the engine *recognizes* event `e` in state `s` and
  interprets it as a transition to `s'`;
* `step s e = none` means `e` is *unrecognized* in state `s` (outside the engine's
  coverage);
* `bail s` is the isolation/quarantine state entered from `s` when the engine gives up;
* `Safe` is the safety invariant the engine is supposed to maintain. -/
structure Engine (Event State : Type) where
  /-- Partial transition function; `none` marks an unrecognized event. -/
  step : State → Event → Option State
  /-- Transition taken when the engine bails out. -/
  bail : State → State
  /-- The safety invariant maintained by the engine. -/
  Safe : State → Prop

variable {Event State : Type}

/-- Actual behaviour of the engine on a trace: interpret recognized events one by one, and
bail out (discarding the rest of the trace) at the first unrecognized event. -/

theorem demoEngine_sound (s : ℕ) (es : List ℕ) (hs : s ≤ 3) : demoEngine.run s es ≤ 3 :=
  (bail_on_unrecognized_is_sound demoEngine demoEngine_step_safe demoEngine_bail_safe).1 s es hs

end PCA.Coverage

