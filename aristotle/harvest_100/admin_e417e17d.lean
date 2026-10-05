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
# Bail On Unrecognized Is Sound
Category: Proof-Carrying Apps
Target: PCA.Coverage.bail_on_unrecognized_is_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA.Coverage

universe u v

/-- The result of executing one step (or a whole trace) of the isolation engine:
either it produced a new state, or it *bailed* because it met an action it did
not recognize. -/
inductive Outcome (State : Type u) : Type u
  | ok (s : State) : Outcome State
  | bail : Outcome State

/-- An isolation engine: a decidable recognizer for the fragment of actions it
claims to cover, together with the transition function it uses on recognized
actions.  Unrecognized actions are *not* modelled here — the engine bails. -/
structure Engine (State : Type u) (Action : Type v) where
  /-- The set of actions the engine claims to cover. -/
  recognize : Action → Bool
  /-- The transition function used on recognized actions. -/
  handler : Action → State → State

variable {State : Type u} {Action : Type v}

/-- One step of the engine: run the handler on a recognized action, bail
otherwise. -/
def Engine.step (E : Engine State Action) (s : State) (a : Action) : Outcome State :=
  if E.recognize a then Outcome.ok (E.handler a s) else Outcome.bail

/-- Run the engine on a whole trace of actions, bailing as soon as an
unrecognized action is encountered. -/
def Engine.run (E : Engine State Action) : State → List Action → Outcome State
  | s, [] => Outcome.ok s
  | s, a :: rest =>
      match E.step s a with
      | Outcome.ok s' => E.run s' rest
      | Outcome.bail => Outcome.bail

@[simp] theorem Engine.run_nil (E : Engine State Action) (s : State) :
    E.run s [] = Outcome.ok s := rfl

theorem Engine.run_cons (E : Engine State Action) (s : State) (a : Action)
    (rest : List Action) :
    E.run s (a :: rest) =
      match E.step s a with
      | Outcome.ok s' => E.run s' rest
      | Outcome.bail => Outcome.bail := rfl

@[simp] theorem Engine.step_of_recognize (E : Engine State Action) (s : State) {a : Action}
    (ha : E.recognize a = true) : E.step s a = Outcome.ok (E.handler a s) := by
  simp [Engine.step, ha]

@[simp] theorem Engine.step_of_not_recognize (E : Engine State Action) (s : State) {a : Action}
    (ha : E.recognize a = false) : E.step s a = Outcome.bail := by
  simp [Engine.step, ha]

/-- The engine really does bail on any trace containing an unrecognized action.
This is the coverage side condition that makes the soundness theorem
meaningful: the engine never silently continues past something it does not
model. -/
theorem Engine.run_eq_bail_of_mem_unrecognized (E : Engine State Action) :
    ∀ (s : State) (as : List Action) (a : Action),
      a ∈ as → E.recognize a = false → E.run s as = Outcome.bail := by
  intro s as
  induction as generalizing s with
  | nil => intro a ha _; cases ha
  | cons b rest ih =>
      intro a ha hrec
      cases ha with
      | head => rw [Engine.run_cons, Engine.step_of_not_recognize _ _ hrec]
      | tail _ ha' =>
          cases hb : E.recognize b with
          | true =>
              rw [Engine.run_cons, Engine.step_of_recognize _ _ hb]
              exact ih _ a ha' hrec
          | false => rw [Engine.run_cons, Engine.step_of_not_recognize _ _ hb]

/-- A *safety certificate* for an engine with respect to a state invariant
`Safe`: every action the engine recognizes preserves the invariant. -/
def Certified (E : Engine State Action) (Safe : State → Prop) : Prop :=
  ∀ (a : Action) (s : State), E.recognize a = true → Safe s → Safe (E.handler a s)

/-- Contrapositive form of soundness: if a certified engine finishes a trace in
an *unsafe* state, then it must have started in an unsafe state. -/
theorem unsafe_result_implies_unsafe_start (E : Engine State Action) (Safe : State → Prop)
    (hcert : Certified E Safe) :
    ∀ (as : List Action) (s s' : State), E.run s as = Outcome.ok s' → ¬ Safe s' → ¬ Safe s := by
  intro as
  induction as with
  | nil =>
      intro s s' hrun hunsafe
      rw [Engine.run_nil] at hrun
      cases hrun
      exact hunsafe
  | cons a rest ih =>
      intro s s' hrun hunsafe hs
      cases ha : E.recognize a with
      | true =>
          rw [Engine.run_cons, Engine.step_of_recognize _ _ ha] at hrun
          exact ih _ _ hrun hunsafe (hcert a s ha hs)
      | false =>
          rw [Engine.run_cons, Engine.step_of_not_recognize _ _ ha] at hrun
          exact Outcome.noConfusion hrun

/-- **Bailing on unrecognized actions is sound.**

If an isolation engine bails on every action outside the fragment it models,
and every action it *does* model preserves the safety invariant `Safe`
(i.e. `Certified E Safe`), then every state the engine successfully reaches
from a safe state is safe. -/
theorem bail_on_unrecognized_is_sound (E : Engine State Action) (Safe : State → Prop)
    (hcert : Certified E Safe) (s s' : State) (as : List Action)
    (hs : Safe s) (hrun : E.run s as = Outcome.ok s') : Safe s' :=
  Classical.byContradiction fun hcon =>
    unsafe_result_implies_unsafe_start E Safe hcert as s s' hrun hcon hs

/-- Complement of the soundness theorem: a successful run only ever visits
recognized actions, so the guarantee above is genuinely about traces the engine
has modelled. -/
theorem all_recognized_of_run_ok (E : Engine State Action) :
    ∀ (as : List Action) (s s' : State), E.run s as = Outcome.ok s' →
      ∀ a ∈ as, E.recognize a = true := by
  intro as s s' hrun a ha
  cases hrec : E.recognize a with
  | true => rfl
  | false =>
      rw [E.run_eq_bail_of_mem_unrecognized s as a ha hrec] at hrun
      exact Outcome.noConfusion hrun

end PCA.Coverage

