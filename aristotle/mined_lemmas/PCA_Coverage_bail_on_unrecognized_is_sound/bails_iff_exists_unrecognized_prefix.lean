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

theorem bails_iff_exists_unrecognized_prefix (E : Engine Event State) :
    ∀ (s : State) (es : List Event),
      E.Bails s es ↔
        ∃ (p : List Event) (e : Event) (q : List Event) (t : State),
          es = p ++ e :: q ∧ E.runOpt s p = some t ∧ E.step t e = none := by
  intro s es
  induction es generalizing s with
  | nil =>
      constructor
      · intro h
        exact absurd h (by simp [Engine.Bails])
      · rintro ⟨p, e, q, t, hp, -, -⟩
        exact absurd hp.symm (by simp)
  | cons e es ih =>
      cases hse : E.step s e with
      | none =>
          constructor
          · intro _
            exact ⟨[], e, es, s, by simp, by simp, hse⟩
          · intro _
            simpa [Engine.Bails] using E.runOpt_cons_of_step_eq_none es hse
      | some s' =>
          constructor
          · intro h
            have h' : E.Bails s' es := by
              simpa [Engine.Bails, E.runOpt_cons_of_step_eq_some es hse] using h
            obtain ⟨p, e', q, t, hpq, hrun, hstep⟩ := (ih s').1 h'
            refine ⟨e :: p, e', q, t, by simp [hpq], ?_, hstep⟩
            rw [E.runOpt_cons_of_step_eq_some p hse]
            exact hrun
          · rintro ⟨p, e', q, t, hpq, hrun, hstepnone⟩
            cases p with
            | nil =>
                simp only [List.nil_append, List.cons.injEq] at hpq
                obtain ⟨he, -⟩ := hpq
                have hts : s = t := by simpa using hrun
                subst hts
                rw [← he] at hstepnone
                simp [hse] at hstepnone
            | cons a p =>
                simp only [List.cons_append, List.cons.injEq] at hpq
                obtain ⟨ha, hq⟩ := hpq
                subst ha
                rw [E.runOpt_cons_of_step_eq_some p hse] at hrun
                have : E.Bails s' es :=
                  (ih s').2 ⟨p, e', q, t, hq, hrun, hstepnone⟩
                simpa [Engine.Bails, E.runOpt_cons_of_step_eq_some es hse] using this

/-! ### Main theorem -/

/-- **Soundness of the bail-on-unrecognized isolation policy.**

Assuming only that

* every *recognized* step preserves the safety invariant (`hstep`), and
* the bail transition preserves the safety invariant (`hbail`),

the engine that bails on unrecognized input is sound and does not over-approximate:

1. *(safety)* starting from any safe state, the invariant holds of the final state after
   running **any** trace, including traces containing events outside the engine's coverage;
2. *(no spurious bailing)* on a fully covered trace the engine reproduces exactly the
   idealized semantics;
3. *(bailing is exactly unrecognition)* the engine bails on a trace if and only if the trace
   really contains an unrecognized event reached along the idealized semantics. -/
