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
