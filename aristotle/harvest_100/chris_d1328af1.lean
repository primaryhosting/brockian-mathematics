/-
# Symmetric On Core
Category: Gate1 Operator
Target: Brockian.DilationGenerator.symmetric_on_core
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian
namespace DilationGenerator

open MeasureTheory Complex

/-- The auxiliary "boundary" function `x ↦ i · x · f x · conj (g x)`, whose derivative is
exactly the difference of the two integrands. -/
private noncomputable def bdry (f g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => Complex.I * (x : ℂ) * f x * (starRingEnd ℂ) (g x)

private theorem hasDerivAt_bdry {f g : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : ℝ) :
    HasDerivAt (bdry f g)
      (Complex.I * (f x * (starRingEnd ℂ) (g x)
        + (x : ℂ) * (deriv f x * (starRingEnd ℂ) (g x)
          + f x * (starRingEnd ℂ) (deriv g x)))) x := by
  have hfd : HasDerivAt f (deriv f x) x :=
    (hf.differentiable (by simp) x).hasDerivAt
  have hgd : HasDerivAt g (deriv g x) x :=
    (hg.differentiable (by simp) x).hasDerivAt
  have hgc : HasDerivAt (fun y : ℝ => (starRingEnd ℂ) (g y)) ((starRingEnd ℂ) (deriv g x)) x :=
    hgd.star
  have hx : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
  have h1 : HasDerivAt (fun y : ℝ => Complex.I * (y : ℂ)) (Complex.I * 1) x :=
    hx.const_mul Complex.I
  have h2 := (h1.mul hfd).mul hgc
  refine HasDerivAt.congr_deriv (f := bdry f g) h2 ?_
  simp only [Pi.mul_apply]
  ring

/-- **Symmetry of the Berry–Keating dilation generator on the smooth compactly supported core.**

For `f, g : ℝ → ℂ` smooth with compact support contained in `(0, ∞)`,
`∫ (A f) · conj g = ∫ f · conj (A g)` on `(0, ∞)`, where `A f = i·((1/2)·f + x·f')`.

This is symmetry on the core only; no self-adjointness is claimed.

Note: the hypotheses `HasCompactSupport g`, `tsupport f ⊆ Set.Ioi 0` and `tsupport g ⊆ Set.Ioi 0`,
which are part of the requested statement, turn out not to be needed for the proof (the boundary
term at `0` vanishes because of the factor `x`, and compact support of `f` alone already makes all
integrands compactly supported); they are kept because they describe the intended core. -/
theorem symmetric_on_core (f g : ℝ → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hfc : HasCompactSupport f) (_hgc : HasCompactSupport g)
    (_hfs : tsupport f ⊆ Set.Ioi 0) (_hgs : tsupport g ⊆ Set.Ioi 0) :
    ∫ x in Set.Ioi (0 : ℝ),
        (Complex.I * ((1 / 2) * f x + (x : ℂ) * deriv f x)) * (starRingEnd ℂ) (g x)
      = ∫ x in Set.Ioi (0 : ℝ),
        f x * (starRingEnd ℂ) (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x)) := by
  -- derivative of the boundary function
  have hderiv : ∀ x : ℝ, deriv (bdry f g) x =
      Complex.I * (f x * (starRingEnd ℂ) (g x)
        + (x : ℂ) * (deriv f x * (starRingEnd ℂ) (g x)
          + f x * (starRingEnd ℂ) (deriv g x))) :=
    fun x => (hasDerivAt_bdry hf hg x).deriv
  -- smoothness of the pieces
  have hconjg : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (starRingEnd ℂ) (g y)) :=
    (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.contDiff.of_le le_top |>.comp hg
  have hcd : ContDiff ℝ (1 : ℕ) (bdry f g) := by
    have : ContDiff ℝ (⊤ : ℕ∞) (bdry f g) := by
      exact ((contDiff_const.mul Complex.ofRealCLM.contDiff).mul hf).mul hconjg
    exact this.of_le (by exact_mod_cast le_top)
  have hcs : HasCompactSupport (bdry f g) := by
    have h1 : HasCompactSupport (fun x : ℝ => Complex.I * (x : ℂ) * f x) :=
      HasCompactSupport.mul_left (f' := f) hfc
    exact HasCompactSupport.mul_right (f := fun x : ℝ => Complex.I * (x : ℂ) * f x) h1
  have hzero : ∫ x in Set.Ioi (0 : ℝ), deriv (bdry f g) x = 0 := by
    rw [hcs.integral_Ioi_deriv_eq hcd 0]
    simp [bdry]
  -- integrability of the right-hand integrand and of the derivative
  have hRHScont : Continuous
      (fun x : ℝ => f x * (starRingEnd ℂ) (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x))) := by
    have hcontg' : Continuous (deriv g) := hg.continuous_deriv (by exact_mod_cast le_top)
    have hcf : Continuous f := hf.continuous
    have hcg : Continuous g := hg.continuous
    fun_prop
  have hRHScs : HasCompactSupport
      (fun x : ℝ => f x * (starRingEnd ℂ) (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x))) :=
    HasCompactSupport.mul_right hfc
  have hRHSint : IntegrableOn
      (fun x : ℝ => f x * (starRingEnd ℂ) (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x)))
      (Set.Ioi (0 : ℝ)) :=
    (hRHScont.integrable_of_hasCompactSupport hRHScs).integrableOn
  have hDint : IntegrableOn (deriv (bdry f g)) (Set.Ioi (0 : ℝ)) :=
    ((hcd.continuous_deriv le_rfl).integrable_of_hasCompactSupport hcs.deriv).integrableOn
  have hsplit : ∀ x : ℝ,
      (Complex.I * ((1 / 2) * f x + (x : ℂ) * deriv f x)) * (starRingEnd ℂ) (g x)
        = f x * (starRingEnd ℂ) (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x))
          + deriv (bdry f g) x := by
    intro x
    rw [hderiv x]
    simp only [map_mul, map_add, map_one, map_div₀, map_ofNat, Complex.conj_I,
      Complex.conj_ofReal]
    ring
  calc ∫ x in Set.Ioi (0 : ℝ),
        (Complex.I * ((1 / 2) * f x + (x : ℂ) * deriv f x)) * (starRingEnd ℂ) (g x)
      = ∫ x in Set.Ioi (0 : ℝ),
          (f x * (starRingEnd ℂ) (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x))
            + deriv (bdry f g) x) := by
        simp only [hsplit]
    _ = (∫ x in Set.Ioi (0 : ℝ),
          f x * (starRingEnd ℂ) (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x)))
        + ∫ x in Set.Ioi (0 : ℝ), deriv (bdry f g) x := integral_add hRHSint hDint
    _ = _ := by rw [hzero, add_zero]

end DilationGenerator
end Brockian

#print axioms Brockian.DilationGenerator.symmetric_on_core

