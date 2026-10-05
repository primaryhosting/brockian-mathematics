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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian
namespace DilationGenerator

open MeasureTheory

/-- The auxiliary function `x ↦ x · f x · conj (g x)`, whose derivative packages the
integration-by-parts identity for the Berry–Keating dilation generator. -/
private noncomputable def aux (f g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (x : ℂ) * f x * starRingEnd ℂ (g x)


theorem symmetric_on_core (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (_hfs : tsupport f ⊆ Set.Ioi (0 : ℝ)) (_hgs : tsupport g ⊆ Set.Ioi (0 : ℝ)) :
    ∫ x in Set.Ioi (0 : ℝ),
        (Complex.I * ((1 / 2) * f x + (x : ℂ) * deriv f x)) * starRingEnd ℂ (g x)
      = ∫ x in Set.Ioi (0 : ℝ),
        f x * starRingEnd ℂ (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x)) := by
  set A : ℝ → ℂ := fun x =>
    (Complex.I * ((1 / 2) * f x + (x : ℂ) * deriv f x)) * starRingEnd ℂ (g x) with hA
  set B : ℝ → ℂ := fun x =>
    f x * starRingEnd ℂ (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x)) with hB
  -- continuity of the ingredients
  have hfcont : Continuous f := hf.continuous
  have hgcont : Continuous g := hg.continuous
  have hf'cont : Continuous (deriv f) := by
    have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv f) := ContDiff.deriv' hf
    exact h.continuous
  have hg'cont : Continuous (deriv g) := by
    have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv g) := ContDiff.deriv' hg
    exact h.continuous
  have hAcont : Continuous A := by
    apply Continuous.mul
    · exact continuous_const.mul ((continuous_const.mul hfcont).add
        (Complex.continuous_ofReal.mul hf'cont))
    · exact Complex.continuous_conj.comp hgcont
  have hBcont : Continuous B := by
    apply Continuous.mul hfcont
    exact Complex.continuous_conj.comp (continuous_const.mul
      ((continuous_const.mul hgcont).add (Complex.continuous_ofReal.mul hg'cont)))
  -- compact support
  have hAcs : HasCompactSupport A := by
    refine HasCompactSupport.intro (K := tsupport g) hgc ?_
    intro x hx
    simp [hA, image_eq_zero_of_notMem_tsupport hx]
  have hBcs : HasCompactSupport B := by
    refine HasCompactSupport.intro (K := tsupport f) hfc ?_
    intro x hx
    simp [hB, image_eq_zero_of_notMem_tsupport hx]
  have hAint : IntegrableOn A (Set.Ioi (0 : ℝ)) :=
    (hAcont.integrable_of_hasCompactSupport hAcs).integrableOn
  have hBint : IntegrableOn B (Set.Ioi (0 : ℝ)) :=
    (hBcont.integrable_of_hasCompactSupport hBcs).integrableOn
  -- integral of the derivative of the auxiliary function
  have hkey : ∫ x in Set.Ioi (0 : ℝ), deriv (aux f g) x = 0 := by
    have := HasCompactSupport.integral_Ioi_deriv_eq (contDiff_aux hf hg)
      (hasCompactSupport_aux (g := g) hfc) 0
    simpa [aux] using this
  -- pointwise identity
  have hpoint : ∀ x : ℝ, A x - B x = Complex.I * deriv (aux f g) x := by
    intro x
    have hd : deriv (aux f g) x =
        f x * starRingEnd ℂ (g x) +
          (x : ℂ) * (deriv f x * starRingEnd ℂ (g x) + f x * starRingEnd ℂ (deriv g x)) :=
      (hasDerivAt_aux hf hg x).deriv
    rw [hd, hA, hB]
    simp only [map_mul, map_add, map_one, map_ofNat, map_div₀, Complex.conj_I,
      Complex.conj_ofReal]
    ring
  rw [← sub_eq_zero, ← integral_sub hAint hBint]
  calc ∫ x in Set.Ioi (0 : ℝ), (A x - B x)
      = ∫ x in Set.Ioi (0 : ℝ), Complex.I * deriv (aux f g) x :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = Complex.I * ∫ x in Set.Ioi (0 : ℝ), deriv (aux f g) x := integral_const_mul _ _
    _ = 0 := by rw [hkey, mul_zero]

end DilationGenerator
end Brockian

