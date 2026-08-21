/-!
# Bail On Unrecognized Is Sound
Category: Proof-Carrying Apps
Target: PCA.Coverage.bail_on_unrecognized_is_sound
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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
def Engine.run (E : Engine Event State) : State → List Event → State
  | s, [] => s
  | s, e :: es =>
      match E.step s e with
      | some s' => Engine.run E s' es
      | none => E.bail s

/-- Idealized behaviour of the engine on a trace: defined exactly on the traces that are
fully covered by `step`, i.e. that contain no unrecognized event. -/
def Engine.runOpt (E : Engine Event State) : State → List Event → Option State
  | s, [] => some s
  | s, e :: es =>
      match E.step s e with
      | some s' => Engine.runOpt E s' es
      | none => none

/-- The engine bails somewhere along the trace `es` started in state `s`. -/
def Engine.Bails (E : Engine Event State) (s : State) (es : List Event) : Prop :=
  E.runOpt s es = none

@[simp] theorem Engine.run_nil (E : Engine Event State) (s : State) :
    E.run s [] = s := rfl

@[simp] theorem Engine.runOpt_nil (E : Engine Event State) (s : State) :
    E.runOpt s [] = some s := rfl

theorem Engine.run_cons_of_step_eq_some
    (E : Engine Event State) {s s' : State} {e : Event} (es : List Event)
    (h : E.step s e = some s') : E.run s (e :: es) = E.run s' es := by
  simp [Engine.run, h]

theorem Engine.run_cons_of_step_eq_none
    (E : Engine Event State) {s : State} {e : Event} (es : List Event)
    (h : E.step s e = none) : E.run s (e :: es) = E.bail s := by
  simp [Engine.run, h]

theorem Engine.runOpt_cons_of_step_eq_some
    (E : Engine Event State) {s s' : State} {e : Event} (es : List Event)
    (h : E.step s e = some s') : E.runOpt s (e :: es) = E.runOpt s' es := by
  simp [Engine.runOpt, h]

theorem Engine.runOpt_cons_of_step_eq_none
    (E : Engine Event State) {s : State} {e : Event} (es : List Event)
    (h : E.step s e = none) : E.runOpt s (e :: es) = none := by
  simp [Engine.runOpt, h]

/-! ### Soundness -/

/-- **Invariant preservation.**  If the safety invariant is preserved by every recognized
step and by the bail transition, then it is preserved by the whole run, on an *arbitrary*
trace — in particular on traces containing events outside the engine's coverage. -/
theorem Engine.safe_run (E : Engine Event State)
    (hstep : ∀ (s s' : State) (e : Event), E.Safe s → E.step s e = some s' → E.Safe s')
    (hbail : ∀ s : State, E.Safe s → E.Safe (E.bail s)) :
    ∀ (s : State) (es : List Event), E.Safe s → E.Safe (E.run s es) := by
  intro s es
  induction es generalizing s with
  | nil => intro hs; simpa using hs
  | cons e es ih =>
      intro hs
      cases hse : E.step s e with
      | none =>
          rw [E.run_cons_of_step_eq_none es hse]
          exact hbail s hs
      | some s' =>
          rw [E.run_cons_of_step_eq_some es hse]
          exact ih s' (hstep s s' e hs hse)

/-- **No loss on covered traces.**  On a trace that the engine fully recognizes, the
bail-on-unrecognized engine computes exactly the idealized result: bailing never fires
spuriously. -/
theorem Engine.run_eq_of_runOpt_eq_some (E : Engine Event State) :
    ∀ (s : State) (es : List Event) (t : State), E.runOpt s es = some t → E.run s es = t := by
  intro s es
  induction es generalizing s with
  | nil => intro t h; simpa using h
  | cons e es ih =>
      intro t h
      cases hse : E.step s e with
      | none =>
          rw [E.runOpt_cons_of_step_eq_none es hse] at h
          simp at h
      | some s' =>
          rw [E.runOpt_cons_of_step_eq_some es hse] at h
          rw [E.run_cons_of_step_eq_some es hse]
          exact ih s' t h

/-! ### Completeness of the coverage model -/

/-- **Completeness.**  The engine bails on a trace exactly when the trace genuinely contains
an unrecognized event: there is a prefix that the engine interprets successfully, after
which the next event is outside its coverage. -/
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
theorem bail_on_unrecognized_is_sound (E : Engine Event State)
    (hstep : ∀ (s s' : State) (e : Event), E.Safe s → E.step s e = some s' → E.Safe s')
    (hbail : ∀ s : State, E.Safe s → E.Safe (E.bail s)) :
    (∀ (s : State) (es : List Event), E.Safe s → E.Safe (E.run s es)) ∧
    (∀ (s : State) (es : List Event) (t : State), E.runOpt s es = some t → E.run s es = t) ∧
    (∀ (s : State) (es : List Event),
      E.Bails s es ↔
        ∃ (p : List Event) (e : Event) (q : List Event) (t : State),
          es = p ++ e :: q ∧ E.runOpt s p = some t ∧ E.step t e = none) :=
  ⟨E.safe_run hstep hbail, E.run_eq_of_runOpt_eq_some, bails_iff_exists_unrecognized_prefix E⟩

/-! ### A concrete instance, witnessing non-vacuity

The hypotheses of `bail_on_unrecognized_is_sound` are satisfiable by an engine whose
invariant is *not* trivially true and that really does meet unrecognized events. -/

/-- A toy privilege-tracking engine: state is the current privilege level (kept `≤ 3`),
event `0` is a no-op, event `1` is an escalation request (capped at level `3`), and every
other event is outside the engine's coverage.  Bailing resets to the least privilege. -/
def demoEngine : Engine ℕ ℕ where
  step s e := if e = 0 then some s else if e = 1 then some (min (s + 1) 3) else none
  bail _ := 0
  Safe s := s ≤ 3

theorem demoEngine_step_safe :
    ∀ (s s' : ℕ) (e : ℕ), demoEngine.Safe s → demoEngine.step s e = some s' →
      demoEngine.Safe s' := by
  intro s s' e hs h
  simp only [demoEngine] at hs h ⊢
  by_cases h0 : e = 0
  · simp [h0] at h; omega
  · by_cases h1 : e = 1
    · simp [h1] at h; omega
    · simp [h0, h1] at h

theorem demoEngine_bail_safe : ∀ s : ℕ, demoEngine.Safe s → demoEngine.Safe (demoEngine.bail s) := by
  intro s _; simp [demoEngine]

/-- The invariant of `demoEngine` is not trivially true: some states violate it. -/
theorem demoEngine_Safe_nontrivial : ¬ demoEngine.Safe 4 := by
  simp [demoEngine]

/-- `demoEngine` genuinely bails on a trace containing an unrecognized event. -/
theorem demoEngine_bails : demoEngine.Bails 0 [1, 7, 1] := by
  simp [Engine.Bails, Engine.runOpt, demoEngine]

/-- On a fully covered trace `demoEngine` does not bail and computes the expected state. -/
theorem demoEngine_run_covered : demoEngine.run 0 [1, 1, 0, 1, 1] = 3 := by
  simp [Engine.run, demoEngine]

/-- Soundness applies to the concrete engine: every run from a safe state stays safe. -/
theorem demoEngine_sound (s : ℕ) (es : List ℕ) (hs : s ≤ 3) : demoEngine.run s es ≤ 3 :=
  (bail_on_unrecognized_is_sound demoEngine demoEngine_step_safe demoEngine_bail_safe).1 s es hs

end PCA.Coverage

