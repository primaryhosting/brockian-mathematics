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

import Brockian.Weyl.TestFunction

/-!
# The du Bois-Reymond lemmas

A locally integrable function whose distributional derivative vanishes is almost everywhere
constant; a locally integrable function whose distributional second derivative vanishes is
almost everywhere affine.
-/

open MeasureTheory Filter
open scoped Topology ContDiff NNReal

namespace Brockian.Weyl.DeficiencyODE

/-! ## The du Bois-Reymond lemmas -/

/-- **du Bois-Reymond lemma.**  A locally integrable function whose distributional derivative
vanishes is almost everywhere constant. -/

theorem integral_deriv_mul_primitive_real {ψ : ℝ → ℝ} (hψ : IsTestFunction ψ)
    {g : ℝ → ℝ} (hg : LocallyIntegrable g volume) :
    ∫ x, deriv ψ x * (∫ t in (0:ℝ)..x, g t) = -∫ x, ψ x * g x := by
  set H : ℝ → ℝ := fun x => ∫ t in (0:ℝ)..x, g t with hH
  obtain ⟨R, hR⟩ := hψ.2.isBounded.subset_closedBall (0 : ℝ)
  have hR0 : (0:ℝ) ≤ |R| := abs_nonneg R
  have hR1 : (0:ℝ) ≤ |R| + 1 := by linarith
  set A : ℝ := -(|R| + 1) with hA
  set B : ℝ := |R| + 1 with hB
  have hAB : A ≤ B := by simp only [hA, hB]; linarith
  have habs : ∀ x : ℝ, x ∈ tsupport ψ → |x| ≤ |R| := by
    intro x hmem
    have h1 := hR hmem
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h1
    exact le_trans h1 (le_abs_self R)
  have hmemtsupp : ∀ x : ℝ, x ∈ tsupport ψ → x ∈ Set.Ioc A B := by
    intro x hmem
    have h2 := habs x hmem
    exact ⟨by simp only [hA]; have := neg_le_of_abs_le h2; linarith,
      by simp only [hB]; have := le_of_abs_le h2; linarith⟩
  have hvanψ : ∀ x : ℝ, x ∉ Set.Ioc A B → ψ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hmem => hx (hmemtsupp x hmem))
  have hvandψ : ∀ x : ℝ, x ∉ Set.Ioc A B → deriv ψ x = 0 := by
    intro x hx
    by_contra hne
    exact hx (hmemtsupp x (support_deriv_subset (Function.mem_support.mpr hne)))
  have hvanAbs : ∀ x : ℝ, |R| < |x| → ψ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hmem => absurd (habs x hmem) (not_le.mpr hx))
  have hψA : ψ A = 0 := hvanAbs A (by rw [hA, abs_neg, abs_of_nonneg hR1, hB]; linarith)
  have hψB : ψ B = 0 := hvanAbs B (by rw [abs_of_nonneg hR1, hB]; linarith)
  have h0mem : (0:ℝ) ∈ Set.uIcc A B := by
    rw [Set.uIcc_of_le hAB]
    constructor <;> [simp only [hA]; simp only [hB]] <;> linarith
  have hACH : AbsolutelyContinuousOnInterval H A B :=
    (locallyIntegrable_intervalIntegrable hg A B).absolutelyContinuousOnInterval_intervalIntegral
      h0mem
  have hACψ : AbsolutelyContinuousOnInterval ψ A B := by
    obtain ⟨K, hK⟩ := hψ.exists_lipschitzWith
    exact LipschitzOnWith.absolutelyContinuousOnInterval (K := K) hK.lipschitzOnWith
  have IBP := hACψ.integral_mul_deriv_eq_deriv_mul hACH
  have hae : ∀ᵐ x : ℝ, x ∈ Set.uIoc A B → ψ x * deriv H x = ψ x * g x := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hg] with x hx _
    rw [(hx 0).deriv]
  rw [intervalIntegral.integral_congr_ae hae, hψA, hψB] at IBP
  have e1 : ∫ x, ψ x * g x = ∫ x in A..B, ψ x * g x :=
    (integral_eq_intervalIntegral hAB (fun x hx => by rw [hvanψ x hx]; ring)).symm
  have e2 : ∫ x, deriv ψ x * H x = ∫ x in A..B, deriv ψ x * H x :=
    (integral_eq_intervalIntegral hAB (fun x hx => by rw [hvandψ x hx]; ring)).symm
  rw [e1, e2]
  linarith [IBP]

/-- **Integration by parts** against the primitive of a locally integrable complex function. -/
