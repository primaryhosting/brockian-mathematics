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

lemma summable_tau_series [CompleteSpace A] (H : A) (t : ℝ) (a : A) :
    Summable (fun n : ℕ => (t ^ n / (n ! : ℝ)) • (ad H)^[n] a) := by
  apply Summable.of_norm
  have hs : Summable (fun n : ℕ => ((2 * ‖H‖ * |t|) ^ n / (n ! : ℝ)) * ‖a‖) :=
    (Real.summable_pow_div_factorial _).mul_right _
  refine hs.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
  rw [norm_smul]
  have h1 : ‖(t ^ n / (n ! : ℝ))‖ = |t| ^ n / (n ! : ℝ) := by
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n ! : ℝ))]
  rw [h1]
  calc |t| ^ n / (n ! : ℝ) * ‖(ad H)^[n] a‖
      ≤ |t| ^ n / (n ! : ℝ) * ((2 * ‖H‖) ^ n * ‖a‖) :=
        mul_le_mul_of_nonneg_left (norm_adPow_le H n a) (by positivity)
    _ = ((2 * ‖H‖ * |t|) ^ n / (n ! : ℝ)) * ‖a‖ := by rw [mul_pow]; ring

/-- The commutator of the evolved observable with `b`, expanded term by term. -/
