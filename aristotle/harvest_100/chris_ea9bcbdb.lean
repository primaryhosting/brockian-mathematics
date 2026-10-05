/-
# Symmetric On Core
Category: Gate1 Operator
Target: Brockian.DilationGenerator.symmetric_on_core
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Symmetric On Core
Category: Gate1 Operator
Target: Brockian.DilationGenerator.symmetric_on_core
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open MeasureTheory Set

/-- The pointwise algebraic identity behind the symmetry of the Berry–Keating dilation
generator: the two `1/2`-terms together with the cross term of the Leibniz rule combine into
the derivative of `x ↦ x * f x * conj (g x)` (multiplied by `i`). -/
private lemma dilation_pointwise (x : ℝ) (f g df dg : ℂ) :
    (Complex.I * ((1 / 2) * f + x * df)) * starRingEnd ℂ g
        - f * starRingEnd ℂ (Complex.I * ((1 / 2) * g + x * dg))
      = Complex.I *
          (f * starRingEnd ℂ g + (x : ℂ) * (df * starRingEnd ℂ g + f * starRingEnd ℂ dg)) := by
  simp [map_add, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- **Symmetry of the Berry–Keating dilation generator on the smooth compactly supported core.**

For `f, g : ℝ → ℂ` smooth, compactly supported, with supports inside `(0, ∞)`, the operator
`A f = i * ((1/2) * f + x * f')` satisfies `∫ (A f) * conj g = ∫ f * conj (A g)` on `(0, ∞)`.

This is symmetry on the core only; no self-adjointness is claimed.

The proof is integration by parts: the integrand difference equals `i * (d/dx) (x * f * conj g)`,
whose integral over `(0, ∞)` is `- (0 * f 0 * conj (g 0)) = 0` by
`HasCompactSupport.integral_Ioi_deriv_eq`.

(The hypotheses `hfs`, `hgs` on the supports were requested in the statement; the proof does not
need them, since the boundary term vanishes already because of the factor `x`.) -/
theorem symmetric_on_core (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hfs : tsupport f ⊆ Set.Ioi (0 : ℝ)) (hgs : tsupport g ⊆ Set.Ioi (0 : ℝ)) :
    ∫ x in Set.Ioi (0 : ℝ),
        (Complex.I * ((1 / 2) * f x + x * deriv f x)) * starRingEnd ℂ (g x)
      = ∫ x in Set.Ioi (0 : ℝ),
        f x * starRingEnd ℂ (Complex.I * ((1 / 2) * g x + x * deriv g x)) := by
  -- Basic regularity facts.
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hdf_cont : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hdg_cont : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  have hf_cont : Continuous f := hf1.continuous
  have hg_cont : Continuous g := hg1.continuous
  have hf_diff : ∀ x : ℝ, HasDerivAt f (deriv f x) x := fun x =>
    (hf1.differentiable one_ne_zero x).hasDerivAt
  have hg_diff : ∀ x : ℝ, HasDerivAt g (deriv g x) x := fun x =>
    (hg1.differentiable one_ne_zero x).hasDerivAt
  -- The primitive `F x = x * (f x * conj (g x))`.
  set F : ℝ → ℂ := fun x => (x : ℂ) * (f x * starRingEnd ℂ (g x)) with hF
  have hconj_g : ContDiff ℝ 1 (fun x : ℝ => starRingEnd ℂ (g x)) :=
    (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.comp hg1
  have hF_contDiff : ContDiff ℝ 1 F :=
    Complex.ofRealCLM.contDiff.mul (hf1.mul hconj_g)
  have hconj_gc : HasCompactSupport (fun x : ℝ => starRingEnd ℂ (g x)) :=
    hgc.comp_left (g := fun z : ℂ => starRingEnd ℂ z) (map_zero _)
  have hF_supp : HasCompactSupport F := by
    have : HasCompactSupport (fun x : ℝ => f x * starRingEnd ℂ (g x)) :=
      HasCompactSupport.mul_right (f := f) (f' := fun x : ℝ => starRingEnd ℂ (g x)) hfc
    exact HasCompactSupport.mul_left (f := fun x : ℝ => (x : ℂ)) (f' := _) this
  -- The derivative of `F`.
  have hF_deriv : ∀ x : ℝ, deriv F x
      = f x * starRingEnd ℂ (g x)
        + (x : ℂ) * (deriv f x * starRingEnd ℂ (g x) + f x * starRingEnd ℂ (deriv g x)) := by
    intro x
    have hx : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x))
    have hcg : HasDerivAt (fun t : ℝ => starRingEnd ℂ (g t)) (starRingEnd ℂ (deriv g x)) x := by
      have := (hg_diff x).star
      simpa [Complex.star_def, RCLike.star_def] using this
    have hprod : HasDerivAt (fun t : ℝ => f t * starRingEnd ℂ (g t))
        (deriv f x * starRingEnd ℂ (g x) + f x * starRingEnd ℂ (deriv g x)) x :=
      (hf_diff x).mul hcg
    have hFd : HasDerivAt F
        (1 * (f x * starRingEnd ℂ (g x))
          + (x : ℂ) * (deriv f x * starRingEnd ℂ (g x) + f x * starRingEnd ℂ (deriv g x))) x :=
      hx.mul hprod
    simpa using hFd.deriv
  -- The integral of `deriv F` over `(0, ∞)` vanishes.
  have hint_deriv : ∫ x in Set.Ioi (0 : ℝ), deriv F x = 0 := by
    have := HasCompactSupport.integral_Ioi_deriv_eq hF_contDiff hF_supp 0
    simpa [hF] using this
  -- Integrability of the two integrands.
  set P : ℝ → ℂ := fun x =>
    (Complex.I * ((1 / 2) * f x + x * deriv f x)) * starRingEnd ℂ (g x) with hP
  set Q : ℝ → ℂ := fun x =>
    f x * starRingEnd ℂ (Complex.I * ((1 / 2) * g x + x * deriv g x)) with hQ
  have hP_cont : Continuous P := by
    fun_prop
  have hQ_cont : Continuous Q := by
    fun_prop
  have hP_supp : HasCompactSupport P :=
    HasCompactSupport.mul_left
      (f := fun x : ℝ => Complex.I * ((1 / 2) * f x + x * deriv f x)) (f' := _) hconj_gc
  have hQ_supp : HasCompactSupport Q :=
    HasCompactSupport.mul_right (f := f) (f' := _) hfc
  have hP_int : IntegrableOn P (Set.Ioi (0 : ℝ)) :=
    (hP_cont.integrable_of_hasCompactSupport hP_supp).integrableOn
  have hQ_int : IntegrableOn Q (Set.Ioi (0 : ℝ)) :=
    (hQ_cont.integrable_of_hasCompactSupport hQ_supp).integrableOn
  -- Put everything together.
  have hdiff : (∫ x in Set.Ioi (0 : ℝ), P x) - ∫ x in Set.Ioi (0 : ℝ), Q x = 0 := by
    rw [← MeasureTheory.integral_sub hP_int hQ_int]
    have hcongr : ∀ x ∈ Set.Ioi (0 : ℝ), P x - Q x = Complex.I * deriv F x := by
      intro x _
      rw [hF_deriv x]
      exact dilation_pointwise x (f x) (g x) (deriv f x) (deriv g x)
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr,
      MeasureTheory.integral_const_mul, hint_deriv, mul_zero]
  exact sub_eq_zero.mp hdiff

end DilationGenerator
end Brockian

#print axioms Brockian.DilationGenerator.symmetric_on_core

