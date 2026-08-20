import Mathlib
/-!
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open MeasureTheory Set

/-! ### The Ma–Trudinger–Wang condition (Loeper's form) -/

section MTW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The quadratic transport cost `c(x,y) = ‖x - y‖²/2`. -/

theorem figalli_OT_regularity
    {f g : ℝ → ℝ≥0∞} {lam Lam : ℝ≥0} (hlam : 0 < lam)
    (hfub : ∀ x, f x ≤ Lam) (hglb : ∀ y, (lam : ℝ≥0∞) ≤ g y)
    {T : ℝ → ℝ}
    (hopt : ∀ x y : ℝ,
      quadCost x (T x) + quadCost y (T y) ≤ quadCost x (T y) + quadCost y (T x))
    (hpush : Measure.map T (volume.withDensity f) = volume.withDensity g) :
    LipschitzWith (Lam / lam) T := by
  have hTmono : Monotone T := monotone_of_quadCost_cyclMonotone hopt
  have hTmeas : Measurable T := hTmono.measurable
  have hlam0 : (lam : ℝ≥0∞) ≠ 0 := by
    simpa using hlam.ne'
  have hlamtop : (lam : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have key : ∀ x y : ℝ, x ≤ y → T y - T x ≤ ((Lam / lam : ℝ≥0) : ℝ) * (y - x) := by
    intro x y hxy
    have h1 : (lam : ℝ≥0∞) * ENNReal.ofReal (T y - T x)
        ≤ (volume.withDensity g) (Icc (T x) (T y)) := le_withDensity_Icc hglb _ _
    have h2 : (volume.withDensity g) (Icc (T x) (T y))
        = (volume.withDensity f) (T ⁻¹' Icc (T x) (T y)) := by
      rw [← hpush, Measure.map_apply hTmeas measurableSet_Icc]
    have hz : ∀ a : ℝ, (volume.withDensity f) (T ⁻¹' {a}) = 0 := by
      intro a
      have h : (volume.withDensity f) (T ⁻¹' {a}) = (volume.withDensity g) {a} := by
        rw [← hpush, Measure.map_apply hTmeas (measurableSet_singleton a)]
      rw [h, withDensity_singleton]
    have h3 : (volume.withDensity f) (T ⁻¹' Icc (T x) (T y))
        ≤ (volume.withDensity f) (Icc x y) := by
      calc (volume.withDensity f) (T ⁻¹' Icc (T x) (T y))
          ≤ (volume.withDensity f) (Icc x y ∪ (T ⁻¹' {T x} ∪ T ⁻¹' {T y})) :=
            measure_mono (preimage_Icc_subset hTmono x y)
        _ ≤ (volume.withDensity f) (Icc x y)
            + (volume.withDensity f) (T ⁻¹' {T x} ∪ T ⁻¹' {T y}) := measure_union_le _ _
        _ ≤ (volume.withDensity f) (Icc x y)
            + ((volume.withDensity f) (T ⁻¹' {T x})
              + (volume.withDensity f) (T ⁻¹' {T y})) := by
            gcongr
            exact measure_union_le _ _
        _ = (volume.withDensity f) (Icc x y) := by rw [hz, hz]; simp
    have h4 : (volume.withDensity f) (Icc x y) ≤ (Lam : ℝ≥0∞) * ENNReal.ofReal (y - x) :=
      withDensity_Icc_le hfub _ _
    have h5 : (lam : ℝ≥0∞) * ENNReal.ofReal (T y - T x)
        ≤ (lam : ℝ≥0∞) * (((Lam / lam : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (y - x)) := by
      have hcancel : (lam : ℝ≥0∞) * ((Lam / lam : ℝ≥0) : ℝ≥0∞) = (Lam : ℝ≥0∞) := by
        rw [← ENNReal.coe_mul, mul_div_cancel₀ _ hlam.ne']
      rw [← mul_assoc, hcancel]
      exact le_trans h1 (le_trans (le_of_eq h2) (le_trans h3 h4))
    have h6 : ENNReal.ofReal (T y - T x)
        ≤ ((Lam / lam : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (y - x) :=
      (ENNReal.mul_le_mul_iff_right hlam0 hlamtop).mp h5
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)] at h6
    exact (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (by positivity) (by linarith))).mp h6
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rcases le_total x y with h | h
  · rw [Real.dist_eq, Real.dist_eq, abs_sub_comm (T x), abs_sub_comm x,
      abs_of_nonneg (sub_nonneg.mpr (hTmono h)), abs_of_nonneg (sub_nonneg.mpr h)]
    exact key x y h
  · rw [Real.dist_eq, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr (hTmono h)), abs_of_nonneg (sub_nonneg.mpr h)]
    exact key y x h

/--
A quantitative consequence: under the hypotheses of `Frontier.figalli_OT_regularity`, the
optimal transport map is differentiable at Lebesgue-almost every point, with derivative
bounded by `Λ/λ`.
-/
