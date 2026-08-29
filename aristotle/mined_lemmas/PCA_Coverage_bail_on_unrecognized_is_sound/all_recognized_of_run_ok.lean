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

