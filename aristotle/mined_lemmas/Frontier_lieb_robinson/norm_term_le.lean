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

lemma norm_term_le (H : A) (t : ℝ) (a b : A) (n : ℕ) :
    ‖(t ^ n / (n ! : ℝ)) • ((ad H)^[n] a * b - b * (ad H)^[n] a)‖
      ≤ 2 * ‖a‖ * ‖b‖ * ((2 * ‖H‖ * |t|) ^ n / (n ! : ℝ)) := by
  have hK : ‖(ad H)^[n] a * b - b * (ad H)^[n] a‖ ≤ 2 * ((2 * ‖H‖) ^ n * ‖a‖) * ‖b‖ := by
    calc ‖(ad H)^[n] a * b - b * (ad H)^[n] a‖
        ≤ ‖(ad H)^[n] a * b‖ + ‖b * (ad H)^[n] a‖ := norm_sub_le _ _
      _ ≤ ‖(ad H)^[n] a‖ * ‖b‖ + ‖b‖ * ‖(ad H)^[n] a‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = 2 * ‖(ad H)^[n] a‖ * ‖b‖ := by ring
      _ ≤ 2 * ((2 * ‖H‖) ^ n * ‖a‖) * ‖b‖ := by
          have := norm_adPow_le H n a
          nlinarith [norm_nonneg b, norm_nonneg ((ad H)^[n] a)]
  rw [norm_smul]
  have h1 : ‖(t ^ n / (n ! : ℝ))‖ = |t| ^ n / (n ! : ℝ) := by
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n ! : ℝ))]
  rw [h1]
  calc |t| ^ n / (n ! : ℝ) * ‖(ad H)^[n] a * b - b * (ad H)^[n] a‖
      ≤ |t| ^ n / (n ! : ℝ) * (2 * ((2 * ‖H‖) ^ n * ‖a‖) * ‖b‖) :=
        mul_le_mul_of_nonneg_left hK (by positivity)
    _ = 2 * ‖a‖ * ‖b‖ * ((2 * ‖H‖ * |t|) ^ n / (n ! : ℝ)) := by rw [mul_pow]; ring

/-- The defining series of `tau` is absolutely convergent. -/
