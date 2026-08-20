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

import Brockian.Weyl.WeakDerivative

/-!
# Weyl deficiency spaces are represented by solutions of the Schrödinger ODE

For a continuous potential `q : ℝ → ℝ` and a spectral parameter `z : ℂ`, consider the
formally symmetric differential expression `τ u = -u'' + q u` on the line.  The minimal
operator is the restriction of `τ` to test functions, and the deficiency space at `z`
consists of the `L²` functions `u` which satisfy `τ u = z u` *weakly*, i.e. in the sense
of distributions:

  `∫ u φ'' = ∫ (q - z) u φ`   for all real test functions `φ`.

The main result of this file, `deficiencyRepresentsODE_of_weakRegularity`, states that
this deficiency space coincides with the set of `L²` functions which agree almost
everywhere with a *classical* (twice differentiable) solution of the ODE
`-u'' + q u = z u`.

The nontrivial inclusion is a regularity statement — every weak solution is almost
everywhere a classical solution — which is proved here from scratch (`weakRegularity`)
from the du Bois-Reymond lemmas of `Brockian.Weyl.WeakDerivative`; consequently the final

theorem integral_deriv_testFunction_mul_primitive (hψ : IsTestFunction ψ)
    (hg : LocallyIntegrable g volume) :
    ∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * (∫ t in (0 : ℝ)..x, g t) = -∫ x : ℝ, (ψ x : ℂ) * g x := by
  obtain ⟨R₁, hR₁0, hR₁⟩ := hψ.2.exists_pos_le_norm
  obtain ⟨R₂, hR₂0, hR₂⟩ := hψ.deriv'.2.exists_pos_le_norm
  set R : ℝ := max R₁ R₂ with hRdef
  have hR0 : 0 < R := lt_of_lt_of_le hR₁0 (le_max_left _ _)
  have hψ0 : ∀ x : ℝ, R ≤ |x| → ψ x = 0 := fun x hx =>
    hR₁ x (by rw [Real.norm_eq_abs]; exact le_trans (le_max_left _ _) hx)
  have hdψ0 : ∀ x : ℝ, R ≤ |x| → deriv ψ x = 0 := fun x hx =>
    hR₂ x (by rw [Real.norm_eq_abs]; exact le_trans (le_max_right _ _) hx)
  set g₀ : ℝ → ℂ := Set.indicator (Set.Icc (-R) R) g with hg₀def
  have hg₀ : Integrable g₀ volume :=
    (hg.integrableOn_isCompact isCompact_Icc).integrable_indicator measurableSet_Icc
  set C : ℂ := ∫ t in Set.Iic (0 : ℝ), g₀ t with hC
  have hpt : ∀ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * (∫ t in (0 : ℝ)..x, g t)
      = ((deriv ψ x : ℝ) : ℂ) * (∫ t in Set.Iic x, g₀ t) - ((deriv ψ x : ℝ) : ℂ) * C := by
    intro x
    by_cases hx : R ≤ |x|
    · simp [hdψ0 x hx]
    · push_neg at hx
      rw [abs_lt] at hx
      have h1 : ∫ t in (0 : ℝ)..x, g t = ∫ t in (0 : ℝ)..x, g₀ t := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        have htmem : t ∈ Set.Icc (-R) R := by
          rcases le_total (0 : ℝ) x with h | h
          · rw [Set.uIcc_of_le h] at ht
            exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
          · rw [Set.uIcc_of_ge h] at ht
            exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
        simp [hg₀def, Set.indicator_of_mem htmem]
      have h2 : ∫ t in (0 : ℝ)..x, g₀ t
          = (∫ t in Set.Iic x, g₀ t) - ∫ t in Set.Iic (0 : ℝ), g₀ t :=
        (intervalIntegral.integral_Iic_sub_Iic hg₀.integrableOn hg₀.integrableOn).symm
      rw [h1, h2, hC]
      ring
  have hsplit : ∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * (∫ t in (0 : ℝ)..x, g t)
      = (∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * (∫ t in Set.Iic x, g₀ t))
        - ∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * C := by
    rw [← integral_sub (integrable_deriv_mul_Iic hψ hg₀)
      (hψ.deriv'.integrable_mul (continuous_const.locallyIntegrable))]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hzero : ∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * C = 0 := by
    rw [integral_mul_const, hψ.integral_deriv_eq_zero, zero_mul]
  have hlast : ∫ x : ℝ, (ψ x : ℂ) * g₀ x = ∫ x : ℝ, (ψ x : ℂ) * g x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : R ≤ |x|
    · simp [hψ0 x hx]
    · push_neg at hx
      rw [abs_lt] at hx
      simp [hg₀def, Set.indicator_of_mem (show x ∈ Set.Icc (-R) R from ⟨hx.1.le, hx.2.le⟩)]
  rw [hsplit, hzero, sub_zero, integral_deriv_testFunction_mul_Iic hψ hg₀, hlast]

end Primitive

/-! ### du Bois-Reymond lemmas -/

/-- A locally integrable function with vanishing distributional derivative is almost
everywhere constant. -/
