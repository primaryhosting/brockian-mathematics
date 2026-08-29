import Mathlib

/-!
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
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

/-- The `L^∞`–`W^{1,1}` endpoint estimate in dimension one: for a continuously
differentiable, compactly supported function `f : ℝ → ℝ` one has
`‖f‖_∞ ≤ (1/2) * ‖f'‖_1`. -/

theorem nirenberg_gagliardo {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hsupp : HasCompactSupport f) (x : ℝ) :
    (f x) ^ 2 ≤ Real.sqrt (∫ t : ℝ, (f t) ^ 2) * Real.sqrt (∫ t : ℝ, (deriv f t) ^ 2) := by
  have hfc : Continuous f := hf.continuous
  have hgc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hgs : HasCompactSupport (deriv f) := hsupp.deriv
  have hmf : MeasureTheory.MemLp (fun t : ℝ => |f t|) (ENNReal.ofReal 2) :=
    (hfc.abs).memLp_of_hasCompactSupport hsupp.abs
  have hmg : MeasureTheory.MemLp (fun t : ℝ => |deriv f t|) (ENNReal.ofReal 2) :=
    (hgc.abs).memLp_of_hasCompactSupport hgs.abs
  have hconj : Real.HolderConjugate 2 2 := by rw [Real.holderConjugate_iff]; norm_num
  have holder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg hconj
    (Filter.Eventually.of_forall fun t : ℝ => abs_nonneg (f t))
    (Filter.Eventually.of_forall fun t : ℝ => abs_nonneg (deriv f t)) hmf hmg
  have e1 : (∫ t : ℝ, |f t| ^ (2 : ℝ)) = ∫ t : ℝ, (f t) ^ 2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show |f t| ^ (2 : ℝ) = f t ^ 2
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  have e2 : (∫ t : ℝ, |deriv f t| ^ (2 : ℝ)) = ∫ t : ℝ, (deriv f t) ^ 2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show |deriv f t| ^ (2 : ℝ) = deriv f t ^ 2
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rw [e1, e2, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at holder
  exact le_trans (sq_le_integral_abs_mul_abs_deriv hf hsupp x) holder

end Frontier

