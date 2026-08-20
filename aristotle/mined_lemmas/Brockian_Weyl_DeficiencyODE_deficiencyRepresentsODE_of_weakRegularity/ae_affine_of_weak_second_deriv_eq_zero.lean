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

theorem ae_affine_of_weak_second_deriv_eq_zero {w : ℝ → ℂ} (hw : LocallyIntegrable w volume)
    (h : ∀ φ : ℝ → ℝ, IsTestFunction φ → ∫ x : ℝ, ((deriv (deriv φ) x : ℝ) : ℂ) * w x = 0) :
    ∃ c₀ c₁ : ℂ, w =ᵐ[volume] fun x => c₀ + c₁ * x := by
  obtain ⟨ρ, hρ, hρ1⟩ := exists_testFunction_integral_one
  set k : ℂ := ∫ x : ℝ, ((deriv ρ x : ℝ) : ℂ) * w x with hk
  have key : ∀ ψ : ℝ → ℝ, IsTestFunction ψ →
      ∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * w x = (∫ x : ℝ, ψ x : ℝ) * k := by
    intro ψ hψ
    set c : ℝ := ∫ x : ℝ, ψ x with hc
    have hη : IsTestFunction (fun x => ψ x - c * ρ x) :=
      ⟨hψ.1.sub (contDiff_const.mul hρ.1), hψ.2.sub hρ.2.mul_left⟩
    have hη0 : ∫ x : ℝ, (ψ x - c * ρ x) = 0 := by
      rw [integral_sub hψ.integrable (hρ.integrable.const_mul c)]
      simp [integral_const_mul, hρ1, ← hc]
    obtain ⟨θ, hθ, hθd⟩ := exists_testFunction_hasDerivAt hη hη0
    have hψeq : ψ = fun x => deriv θ x + c * ρ x := by
      funext x
      rw [(hθd x).deriv]
      ring
    have hderivψ : deriv ψ = fun x => deriv (deriv θ) x + c * deriv ρ x := by
      funext x
      have h1 : HasDerivAt (deriv θ) (deriv (deriv θ) x) x :=
        (hθ.deriv'.differentiable x).hasDerivAt
      have h2 : HasDerivAt (fun y => c * ρ y) (c * deriv ρ x) x :=
        ((hρ.differentiable x).hasDerivAt).const_mul c
      rw [hψeq]
      exact (h1.add h2).deriv
    rw [hderivψ]
    simp only [Complex.ofReal_add, Complex.ofReal_mul, add_mul]
    rw [integral_add (hθ.deriv'.deriv'.integrable_mul hw)
      (by simpa [mul_assoc] using ((hρ.deriv'.integrable_mul hw).const_mul (c : ℂ))),
      h θ hθ, zero_add, hk, ← integral_const_mul]
    congr 1
    ext x
    ring
  have hV : ∀ ψ : ℝ → ℝ, IsTestFunction ψ →
      ∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * (w x + k * x) = 0 := by
    intro ψ hψ
    have hsplit : ∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * (w x + k * x)
        = (∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * w x)
          + ∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * (k * x) := by
      rw [← integral_add (hψ.deriv'.integrable_mul hw)
        (hψ.deriv'.integrable_mul
          (by fun_prop : Continuous fun x : ℝ => k * (x : ℂ)).locallyIntegrable)]
      congr 1
      ext x
      ring
    have hibp : ∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * (k * x) = -∫ x : ℝ, (ψ x : ℂ) * k := by
      refine integral_deriv_testFunction_mul (F := fun x : ℝ => k * x) (f := fun _ => k)
        (fun x => ?_) continuous_const hψ
      simpa using ((hasDerivAt_id x).ofReal_comp).const_mul k
    rw [hsplit, hibp, key ψ hψ, integral_mul_const, integral_complex_ofReal]
    ring
  obtain ⟨c₀, hc₀⟩ := ae_const_of_weak_deriv_eq_zero
    (hw.add (by fun_prop : Continuous fun x : ℝ => k * (x : ℂ)).locallyIntegrable) hV
  refine ⟨c₀, -k, ?_⟩
  filter_upwards [hc₀] with x hx
  simp only [Pi.add_apply] at hx
  linear_combination hx

end Brockian.Weyl

