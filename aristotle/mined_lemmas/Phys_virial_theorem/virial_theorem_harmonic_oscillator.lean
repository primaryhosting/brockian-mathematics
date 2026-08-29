/-
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter MeasureTheory Topology Complex

namespace Phys

/-- `‖z‖ ^ 2` in terms of the real and imaginary parts of `z`. -/

theorem virial_theorem_harmonic_oscillator :
    2 * ∫ x : ℝ, ‖dpsi x‖ ^ 2 = ∫ x : ℝ, x * dpot x * ‖psi x‖ ^ 2 := by
  have hnorms : ∀ x : ℝ, ‖psi x‖ ^ 2 = Real.exp (-x ^ 2) := norm_psi_sq
  have hnormd : ∀ x : ℝ, ‖dpsi x‖ ^ 2 = x ^ 2 * Real.exp (-x ^ 2) := norm_dpsi_sq
  have hexp : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Real.exp (-y ^ 2 / 2))
      ((-x) * Real.exp (-x ^ 2 / 2)) x := by
    intro x
    have h : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
      have := (hasDerivAt_pow 2 x).neg.div_const 2
      convert this using 1
      ring
    simpa [mul_comm] using h.exp
  refine Phys.virial_theorem psi dpsi ddpsi pot dpot 1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x
    exact (hexp x).ofReal_comp
  · intro x
    have h : HasDerivAt (fun y : ℝ => (-y) * Real.exp (-y ^ 2 / 2))
        ((x ^ 2 - 1) * Real.exp (-x ^ 2 / 2)) x := by
      have h1 : HasDerivAt (fun y : ℝ => -y) (-1 : ℝ) x := by
        simpa using (hasDerivAt_id x).neg
      have h2 := h1.mul (hexp x)
      convert h2 using 1
      ring
    exact h.ofReal_comp
  · intro x
    simpa [pot, dpot] using (hasDerivAt_pow 2 x)
  · intro x
    simp only [psi, ddpsi, pot]
    push_cast
    ring
  · exact integrable_sq_gauss.congr (by filter_upwards with x using (hnormd x).symm)
  · refine (integrable_sq_gauss.sub integrable_gauss).congr ?_
    filter_upwards with x
    simp only [Pi.sub_apply]
    rw [hnorms x, pot]
    ring
  · refine (integrable_sq_gauss.const_mul 2).congr ?_
    filter_upwards with x
    rw [hnorms x, dpot]
    ring
  · refine (tendsto_abs_gauss_atBot).congr fun x => ?_
    rw [psi, dpsi, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_pos _).le, abs_mul, abs_neg, abs_of_nonneg (Real.exp_pos _).le]
    rw [← mul_assoc, mul_comm (Real.exp (-x ^ 2 / 2)) |x|, mul_assoc, exp_half_sq]
  · refine (tendsto_abs_gauss_atTop).congr fun x => ?_
    rw [psi, dpsi, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_pos _).le, abs_mul, abs_neg, abs_of_nonneg (Real.exp_pos _).le]
    rw [← mul_assoc, mul_comm (Real.exp (-x ^ 2 / 2)) |x|, mul_assoc, exp_half_sq]
  · refine squeeze_zero_norm (fun x => ?_) tendsto_abs_gauss_atBot
    rw [hnorms x, hnormd x, pot, Real.norm_eq_abs, abs_mul]
    have : x ^ 2 * Real.exp (-x ^ 2) - (x ^ 2 - 1) * Real.exp (-x ^ 2) = Real.exp (-x ^ 2) := by
      ring
    rw [this, abs_of_nonneg (Real.exp_pos _).le]
  · refine squeeze_zero_norm (fun x => ?_) tendsto_abs_gauss_atTop
    rw [hnorms x, hnormd x, pot, Real.norm_eq_abs, abs_mul]
    have : x ^ 2 * Real.exp (-x ^ 2) - (x ^ 2 - 1) * Real.exp (-x ^ 2) = Real.exp (-x ^ 2) := by
      ring
    rw [this, abs_of_nonneg (Real.exp_pos _).le]

end HarmonicOscillator

end Phys

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

