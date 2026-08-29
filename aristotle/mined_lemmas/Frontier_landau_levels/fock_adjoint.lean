import Mathlib
import RequestProject.Fock
/-!
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

open scoped InnerProductSpace

/-- The cyclotron frequency `ω_c = q B / m` of a particle of charge `q` and mass `m`
in a uniform magnetic field of strength `B`. -/

theorem fock_adjoint (x y : ℕ →₀ ℂ) :
    (inner ℂ (fockB x) y : ℂ) = inner ℂ x (fockA y) := by
  simp only [fock_inner_def]
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => rw [map_add, fockInner_add_left, hp, hq, ← fockInner_add_left]
  | single m c =>
      induction y using Finsupp.induction_linear with
      | zero => simp
      | add p q hp hq =>
          rw [fockInner_add_right, hp, hq, map_add, fockInner_add_right]
      | single k d =>
          rw [fockB_single, fockA_single, fockInner_single_single, fockInner_single_single]
          cases k with
          | zero => simp
          | succ j =>
              simp only [Nat.add_sub_cancel]
              by_cases h : m = j
              · subst h
                simp only [Nat.factorial_succ]
                push_cast
                ring
              · simp [h]

/-- The vacuum (lowest Landau level) state. -/
