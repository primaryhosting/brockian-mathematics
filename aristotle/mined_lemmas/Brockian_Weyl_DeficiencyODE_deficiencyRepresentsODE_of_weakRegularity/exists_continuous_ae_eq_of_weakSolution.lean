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

theorem exists_continuous_ae_eq_of_weakSolution {q : ℝ → ℝ} (hq : Continuous q) {z : ℂ}
    {u : ℝ → ℂ} (hu : LocallyIntegrable u volume) (hweak : WeakSolution q z u) :
    ∃ v : ℝ → ℂ, Continuous v ∧ u =ᵐ[volume] v := by
  set g : ℝ → ℂ := fun x => ((q x : ℂ) - z) * u x with hg
  have hgl : LocallyIntegrable g volume := by
    rw [← locallyIntegrableOn_univ] at hu ⊢
    exact hu.continuousOn_mul
      (((Complex.continuous_ofReal.comp hq).sub continuous_const).continuousOn)
      isClosed_univ.isLocallyClosed
  set G₁ : ℝ → ℂ := fun x => ∫ t in (0 : ℝ)..x, g t with hG₁
  have hG₁c : Continuous G₁ :=
    intervalIntegral.continuous_primitive
      (fun a b => (hgl.integrableOn_isCompact isCompact_uIcc).intervalIntegrable) 0
  set G₂ : ℝ → ℂ := fun x => ∫ t in (0 : ℝ)..x, G₁ t with hG₂
  have hG₂d : ∀ x, HasDerivAt G₂ (G₁ x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hG₁c.intervalIntegrable _ _)
      (hG₁c.stronglyMeasurableAtFilter _ _) hG₁c.continuousAt
  have hG₂c : Continuous G₂ := continuous_iff_continuousAt.mpr fun x => (hG₂d x).continuousAt
  have hG₂weak : ∀ φ : ℝ → ℝ, IsTestFunction φ →
      ∫ x : ℝ, ((deriv (deriv φ) x : ℝ) : ℂ) * G₂ x = ∫ x : ℝ, (φ x : ℂ) * g x := by
    intro φ hφ
    rw [integral_deriv_testFunction_mul hG₂d hG₁c hφ.deriv',
      integral_deriv_testFunction_mul_primitive hφ hgl, neg_neg]
  have hdiff : ∀ φ : ℝ → ℝ, IsTestFunction φ →
      ∫ x : ℝ, ((deriv (deriv φ) x : ℝ) : ℂ) * (u x - G₂ x) = 0 := by
    intro φ hφ
    have hsplit : ∫ x : ℝ, ((deriv (deriv φ) x : ℝ) : ℂ) * (u x - G₂ x)
        = (∫ x : ℝ, ((deriv (deriv φ) x : ℝ) : ℂ) * u x)
          - ∫ x : ℝ, ((deriv (deriv φ) x : ℝ) : ℂ) * G₂ x := by
      rw [← integral_sub (hφ.deriv'.deriv'.integrable_mul hu)
        (hφ.deriv'.deriv'.integrable_mul hG₂c.locallyIntegrable)]
      congr 1
      ext x
      ring
    rw [hsplit, hweak φ hφ, hG₂weak φ hφ, sub_self]
  obtain ⟨c₀, c₁, hc⟩ := ae_affine_of_weak_second_deriv_eq_zero
    (hu.sub hG₂c.locallyIntegrable) hdiff
  refine ⟨fun x => G₂ x + (c₀ + c₁ * x), by fun_prop, ?_⟩
  filter_upwards [hc] with x hx
  have hx' : u x - G₂ x = c₀ + c₁ * x := hx
  linear_combination hx'

/-- **Weak regularity**: every locally integrable distributional solution of
`-u'' + q u = z u` agrees almost everywhere with a classical solution.  This is the
hypothesis that the main theorem used to assume. -/
