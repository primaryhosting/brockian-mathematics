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

theorem ae_const_of_weak_deriv_eq_zero {v : ℝ → ℂ} (hv : LocallyIntegrable v volume)
    (h : ∀ ψ : ℝ → ℝ, IsTestFunction ψ → ∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * v x = 0) :
    ∃ c : ℂ, v =ᵐ[volume] fun _ => c := by
  obtain ⟨ρ, hρ, hρ1⟩ := exists_testFunction_integral_one
  set k : ℂ := ∫ x : ℝ, (ρ x : ℂ) * v x with hk
  refine ⟨k, ?_⟩
  have key : ∀ ψ : ℝ → ℝ, IsTestFunction ψ →
      ∫ x : ℝ, (ψ x : ℂ) * v x = ∫ x : ℝ, (ψ x : ℂ) * k := by
    intro ψ hψ
    set c : ℝ := ∫ x : ℝ, ψ x with hc
    have hη : IsTestFunction (fun x => ψ x - c * ρ x) :=
      ⟨hψ.1.sub (contDiff_const.mul hρ.1), hψ.2.sub hρ.2.mul_left⟩
    have hη0 : ∫ x : ℝ, (ψ x - c * ρ x) = 0 := by
      rw [integral_sub hψ.integrable (hρ.integrable.const_mul c)]
      simp [integral_const_mul, hρ1, ← hc]
    obtain ⟨θ, hθ, hθd⟩ := exists_testFunction_hasDerivAt hη hη0
    have hdθ : deriv θ = fun x => ψ x - c * ρ x := funext fun x => (hθd x).deriv
    have hz := h θ hθ
    rw [hdθ] at hz
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, sub_mul] at hz
    rw [integral_sub (hψ.integrable_mul hv)
      (by simpa [mul_assoc] using ((hρ.integrable_mul hv).const_mul (c : ℂ)))] at hz
    have h2 : ∫ x : ℝ, (c : ℂ) * (ρ x : ℂ) * v x = (c : ℂ) * k := by
      rw [hk, ← integral_const_mul]; congr 1; ext x; ring
    rw [h2, sub_eq_zero] at hz
    rw [hz, integral_mul_const, integral_complex_ofReal]
  refine ae_eq_of_integral_contDiff_smul_eq hv continuous_const.locallyIntegrable ?_
  intro g hg hgc
  simpa only [Complex.real_smul] using key g ⟨hg, hgc⟩

/-- A locally integrable function whose second distributional derivative vanishes is
almost everywhere affine. -/
