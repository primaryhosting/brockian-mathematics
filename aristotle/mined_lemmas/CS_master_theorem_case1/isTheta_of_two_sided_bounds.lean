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

set_option grind.warning false

namespace CS

/-- `(b^k)^(log_b a) = a^k`. -/

lemma isTheta_of_two_sided_bounds (S g : ℕ → ℝ) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁)
    (hg : ∀ k, 0 < g k) (h : ∀ k, c₁ * g k ≤ S k ∧ S k ≤ c₂ * g k) :
    S =Θ[Filter.atTop] g := by
  constructor
  · refine Asymptotics.IsBigO.of_bound c₂ (Filter.Eventually.of_forall fun k => ?_)
    have h1 := (h k).1
    have h2 := (h k).2
    have hgk := hg k
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by nlinarith : (0:ℝ) ≤ S k),
      abs_of_nonneg hgk.le]
    exact h2
  · refine Asymptotics.IsBigO.of_bound c₁⁻¹ (Filter.Eventually.of_forall fun k => ?_)
    have h1 := (h k).1
    have hgk := hg k
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by nlinarith : (0:ℝ) ≤ S k),
      abs_of_nonneg hgk.le]
    have h2 : c₁⁻¹ * (c₁ * g k) ≤ c₁⁻¹ * S k :=
      mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hc₁.le)
    rwa [← mul_assoc, inv_mul_cancel₀ hc₁.ne', one_mul] at h2

/-- **Master theorem, case 1**, stated as a genuine `Θ`-asymptotic along the powers of `b`:
under the hypotheses of `CS.master_theorem_case1`, the map `k ↦ T (b ^ k)` is `Θ` of
`k ↦ (b ^ k) ^ (log_b a)` as `k → ∞`. -/
