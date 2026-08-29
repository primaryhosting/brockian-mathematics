import Mathlib
/-!
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

section Basic

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- The inner derivation (adjoint action) `ad H x = H * x - x * H`. -/

lemma norm_adPow_le (H : A) (n : ℕ) (a : A) :
    ‖(ad H)^[n] a‖ ≤ (2 * ‖H‖) ^ n * ‖a‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc ‖ad H ((ad H)^[n] a)‖ ≤ 2 * ‖H‖ * ‖(ad H)^[n] a‖ := norm_ad_le _ _
        _ ≤ 2 * ‖H‖ * ((2 * ‖H‖) ^ n * ‖a‖) :=
            mul_le_mul_of_nonneg_left ih (by positivity)
        _ = (2 * ‖H‖) ^ (n + 1) * ‖a‖ := by ring

/-- Norm bound on the `n`-th term of the commutator expansion. -/
