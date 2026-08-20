import Mathlib

/-!
# Symmetric On Core
Category: Gate1 Operator
Target: Brockian.DilationGenerator.symmetric_on_core
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical
open MeasureTheory Complex

namespace Brockian.DilationGenerator

/-- The Berry–Keating dilation generator `A f = i * ((1/2) f + x f')` is symmetric on the
core of smooth, compactly supported functions with support in `(0, ∞)`:
`∫ (A f) * conj g = ∫ f * conj (A g)` over `(0, ∞)`.

The proof is integration by parts: the difference of the two integrands is
`i * d/dx (x * f x * conj (g x))`, whose integral over `(0, ∞)` equals
`-(0 * f 0 * conj (g 0)) = 0` since the auxiliary function is `C^1` with compact support
and vanishes at `0`.

The support hypotheses `tsupport f ⊆ Set.Ioi 0`, `tsupport g ⊆ Set.Ioi 0` and the compact
support of `g` are stated as requested; they turn out not to be needed for the argument,
because the boundary term at `0` already vanishes thanks to the factor `x` (compact support
of `f` alone suffices for the integrability and decay). -/
theorem symmetric_on_core
    (f g : ℝ → ℂ) (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g)
    (hfc : HasCompactSupport f) (_hgc : HasCompactSupport g)
    (_hfs : tsupport f ⊆ Set.Ioi 0) (_hgs : tsupport g ⊆ Set.Ioi 0) :
    ∫ x in Set.Ioi (0 : ℝ),
        (Complex.I * ((1 / 2) * f x + (x : ℂ) * deriv f x)) * starRingEnd ℂ (g x)
      = ∫ x in Set.Ioi (0 : ℝ),
        f x * starRingEnd ℂ (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x)) := by
  -- the auxiliary function `F x = x * f x * conj (g x)`
  set F : ℝ → ℂ := fun x => (x : ℂ) * (f x * starRingEnd ℂ (g x)) with hF
  have hconjg : ContDiff ℝ (⊤ : ℕ∞) (fun x => starRingEnd ℂ (g x)) := by
    exact Complex.conjCLE.contDiff.comp (hg.of_le le_top)
  have hFcd : ContDiff ℝ (1 : ℕ) F := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
    exact ((h1.mul ((hf.of_le le_top).mul hconjg)).of_le (by exact_mod_cast le_top))
  have hFc : HasCompactSupport F := by
    have : HasCompactSupport (fun x : ℝ => f x * starRingEnd ℂ (g x)) := hfc.mul_right
    exact this.mul_left
  -- derivative of `F`
  have hderivF : ∀ x : ℝ,
      HasDerivAt F (f x * starRingEnd ℂ (g x)
        + (x : ℂ) * (deriv f x * starRingEnd ℂ (g x) + f x * starRingEnd ℂ (deriv g x))) x := by
    intro x
    have hx : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
      simpa using Complex.ofRealCLM.hasDerivAt (x := x)
    have hfx : HasDerivAt f (deriv f x) x := (hf.differentiable (by simp) x).hasDerivAt
    have hgx : HasDerivAt g (deriv g x) x := (hg.differentiable (by simp) x).hasDerivAt
    have hcg : HasDerivAt (fun t : ℝ => starRingEnd ℂ (g t)) (starRingEnd ℂ (deriv g x)) x := by
      simpa [Complex.star_def] using hgx.star
    simpa using hx.mul (hfx.mul hcg)
  have hderivF' : ∀ x : ℝ, deriv F x
      = f x * starRingEnd ℂ (g x)
        + (x : ℂ) * (deriv f x * starRingEnd ℂ (g x) + f x * starRingEnd ℂ (deriv g x)) :=
    fun x => (hderivF x).deriv
  -- boundary term vanishes
  have hzero : ∫ x in Set.Ioi (0 : ℝ), deriv F x = 0 := by
    rw [hFc.integral_Ioi_deriv_eq hFcd 0]
    simp [hF]
  -- pointwise identity
  have hpt : ∀ x : ℝ,
      (Complex.I * ((1 / 2) * f x + (x : ℂ) * deriv f x)) * starRingEnd ℂ (g x)
        = f x * starRingEnd ℂ (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x))
          + Complex.I * deriv F x := by
    intro x
    rw [hderivF' x]
    simp only [map_add, map_mul, Complex.conj_I, map_div₀, map_one, map_ofNat,
      Complex.conj_ofReal]
    ring
  -- integrability
  have hcf : Continuous f := hf.continuous
  have hcg' : Continuous g := hg.continuous
  have hcdg : Continuous (deriv g) := hg.continuous_deriv le_top
  have hint_rhs : IntegrableOn
      (fun x : ℝ => f x * starRingEnd ℂ (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x)))
      (Set.Ioi (0 : ℝ)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · exact hfc.mul_right
  have hint_der : IntegrableOn (fun x : ℝ => Complex.I * deriv F x) (Set.Ioi (0 : ℝ)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · have : Continuous (deriv F) := hFcd.continuous_deriv le_rfl
      fun_prop
    · exact (hFc.deriv).mul_left
  calc
    ∫ x in Set.Ioi (0 : ℝ),
        (Complex.I * ((1 / 2) * f x + (x : ℂ) * deriv f x)) * starRingEnd ℂ (g x)
        = ∫ x in Set.Ioi (0 : ℝ),
            (f x * starRingEnd ℂ (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x))
              + Complex.I * deriv F x) := by
          exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => hpt x)
    _ = (∫ x in Set.Ioi (0 : ℝ),
            f x * starRingEnd ℂ (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x)))
          + ∫ x in Set.Ioi (0 : ℝ), Complex.I * deriv F x := integral_add hint_rhs hint_der
    _ = ∫ x in Set.Ioi (0 : ℝ),
            f x * starRingEnd ℂ (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x)) := by
          rw [integral_const_mul, hzero]
          simp

end Brockian.DilationGenerator

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

