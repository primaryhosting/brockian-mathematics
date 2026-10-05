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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian
namespace DilationGenerator

open MeasureTheory Set

/-- The core computation: for `f, g` of class `C¹` with compact support, the function
`x ↦ x · f x · conj (g x)` is `C¹` with compact support, so the integral of its derivative
over `(0, ∞)` vanishes.  This is the integration-by-parts identity underlying symmetry of the
Berry–Keating dilation generator. -/
theorem integral_Ioi_leibniz_eq_zero (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hfc : HasCompactSupport f) :
    (∫ x in Ioi (0:ℝ), f x * (starRingEnd ℂ) (g x))
      + (∫ x in Ioi (0:ℝ), (x : ℂ) * deriv f x * (starRingEnd ℂ) (g x))
      + (∫ x in Ioi (0:ℝ), (x : ℂ) * f x * (starRingEnd ℂ) (deriv g x)) = 0 := by
  classical
  set F : ℝ → ℂ := fun x => (x : ℂ) * f x * (starRingEnd ℂ) (g x) with hF
  -- derivative of `F`
  have hfd : ∀ x : ℝ, HasDerivAt f (deriv f x) x := fun x =>
    (hf.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hgd : ∀ x : ℝ, HasDerivAt g (deriv g x) x := fun x =>
    (hg.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hofReal : ∀ x : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
    intro x
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x))
  have hD : ∀ x : ℝ, HasDerivAt F
      (f x * (starRingEnd ℂ) (g x) + (x : ℂ) * deriv f x * (starRingEnd ℂ) (g x)
        + (x : ℂ) * f x * (starRingEnd ℂ) (deriv g x)) x := by
    intro x
    have hstar : HasDerivAt (fun t : ℝ => (starRingEnd ℂ) (g t))
        ((starRingEnd ℂ) (deriv g x)) x := by
      simpa [RCLike.star_def] using (hgd x).star
    have h := (((hofReal x).mul (hfd x)).mul hstar)
    simp only [Pi.mul_apply] at h
    convert h using 1
    ring
  -- smoothness and compact support of `F`
  have hFcd : ContDiff ℝ 1 F := by
    have h1 : ContDiff ℝ 1 (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff.of_le le_top
    have hconj : ContDiff ℝ 1 (fun z : ℂ => (starRingEnd ℂ) z) := by
      simpa [Complex.conjCLE_apply] using (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.of_le le_top
    exact (h1.mul hf).mul (hconj.comp hg)
  have hFcs : HasCompactSupport F := (hfc.mul_left).mul_right
  have hmain : ∫ x in Ioi (0:ℝ), deriv F x = -F 0 :=
    hFcs.integral_Ioi_deriv_eq hFcd 0
  have hderiv : (fun x : ℝ => deriv F x) = fun x : ℝ =>
      f x * (starRingEnd ℂ) (g x) + (x : ℂ) * deriv f x * (starRingEnd ℂ) (g x)
        + (x : ℂ) * f x * (starRingEnd ℂ) (deriv g x) := funext fun x => (hD x).deriv
  have hF0 : F 0 = 0 := by simp [hF]
  rw [hderiv, hF0, neg_zero] at hmain
  -- integrability of the three pieces
  have hcf : Continuous f := hf.continuous
  have hcg : Continuous g := hg.continuous
  have hcf' : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hcg' : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  have hia : Integrable (fun x : ℝ => f x * (starRingEnd ℂ) (g x)) volume :=
    (hcf.mul (Complex.continuous_conj.comp hcg)).integrable_of_hasCompactSupport
      (hfc.mul_right)
  have hib : Integrable (fun x : ℝ => (x : ℂ) * deriv f x * (starRingEnd ℂ) (g x)) volume :=
    (((Complex.continuous_ofReal.mul hcf').mul
      (Complex.continuous_conj.comp hcg))).integrable_of_hasCompactSupport
      ((hfc.deriv.mul_left).mul_right)
  have hid : Integrable (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (deriv g x)) volume :=
    (((Complex.continuous_ofReal.mul hcf).mul
      (Complex.continuous_conj.comp hcg'))).integrable_of_hasCompactSupport
      ((hfc.mul_left).mul_right)
  have h12 : IntegrableOn (fun x : ℝ => f x * (starRingEnd ℂ) (g x)
      + (x : ℂ) * deriv f x * (starRingEnd ℂ) (g x)) (Ioi 0) volume :=
    hia.restrict.add hib.restrict
  rw [← integral_add hia.restrict hib.restrict, ← integral_add h12 hid.restrict]
  exact hmain

/-- **Symmetry of the Berry–Keating dilation generator on a `C¹` compactly supported core.**

For `f` of class `C¹` with compact support and `g` of class `C¹`,
`∫ (A f) · conj g = ∫ f · conj (A g)` on `(0, ∞)`, where `A f = i ((1/2) f + x f')`.
This is the analytic content: it is proved by integration by parts, the boundary term
`x · f x · conj (g x)` vanishing at `0` and at `+∞`. -/
theorem symmetric_on_core_contDiff_one (f g : ℝ → ℂ)
    (hf1 : ContDiff ℝ 1 f) (hg1 : ContDiff ℝ 1 g) (hfc : HasCompactSupport f) :
    ∫ x in Set.Ioi (0:ℝ),
        (Complex.I * ((1/2) * f x + (x : ℂ) * deriv f x)) * starRingEnd ℂ (g x)
      = ∫ x in Set.Ioi (0:ℝ),
        f x * starRingEnd ℂ (Complex.I * ((1/2) * g x + (x : ℂ) * deriv g x)) := by
  classical
  have hcf : Continuous f := hf1.continuous
  have hcg : Continuous g := hg1.continuous
  have hcf' : Continuous (deriv f) := hf1.continuous_deriv (by norm_num)
  have hcg' : Continuous (deriv g) := hg1.continuous_deriv (by norm_num)
  have hia : Integrable (fun x : ℝ => f x * (starRingEnd ℂ) (g x)) volume :=
    (hcf.mul (Complex.continuous_conj.comp hcg)).integrable_of_hasCompactSupport
      (hfc.mul_right)
  have hib : Integrable (fun x : ℝ => (x : ℂ) * deriv f x * (starRingEnd ℂ) (g x)) volume :=
    (((Complex.continuous_ofReal.mul hcf').mul
      (Complex.continuous_conj.comp hcg))).integrable_of_hasCompactSupport
      ((hfc.deriv.mul_left).mul_right)
  have hid : Integrable (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (deriv g x)) volume :=
    (((Complex.continuous_ofReal.mul hcf).mul
      (Complex.continuous_conj.comp hcg'))).integrable_of_hasCompactSupport
      ((hfc.mul_left).mul_right)
  set Ia := ∫ x in Ioi (0:ℝ), f x * (starRingEnd ℂ) (g x) with hIa
  set Ib := ∫ x in Ioi (0:ℝ), (x : ℂ) * deriv f x * (starRingEnd ℂ) (g x) with hIb
  set Id := ∫ x in Ioi (0:ℝ), (x : ℂ) * f x * (starRingEnd ℂ) (deriv g x) with hId
  have key : Ia + Ib + Id = 0 := integral_Ioi_leibniz_eq_zero f g hf1 hg1 hfc
  have hL : ∫ x in Set.Ioi (0:ℝ),
      (Complex.I * ((1/2) * f x + (x : ℂ) * deriv f x)) * starRingEnd ℂ (g x)
      = Complex.I * ((1/2) * Ia + Ib) := by
    have hcongr : ∀ x ∈ Ioi (0:ℝ),
        (Complex.I * ((1/2) * f x + (x : ℂ) * deriv f x)) * starRingEnd ℂ (g x)
          = Complex.I * ((1/2) * (f x * (starRingEnd ℂ) (g x))
              + (x : ℂ) * deriv f x * (starRingEnd ℂ) (g x)) := by
      intro x _
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
      integral_add ((hia.restrict).const_mul _) hib.restrict, integral_const_mul, hIa, hIb]
  have hR : ∫ x in Set.Ioi (0:ℝ),
      f x * starRingEnd ℂ (Complex.I * ((1/2) * g x + (x : ℂ) * deriv g x))
      = -Complex.I * ((1/2) * Ia + Id) := by
    have hcongr : ∀ x ∈ Ioi (0:ℝ),
        f x * starRingEnd ℂ (Complex.I * ((1/2) * g x + (x : ℂ) * deriv g x))
          = -Complex.I * ((1/2) * (f x * (starRingEnd ℂ) (g x))
              + (x : ℂ) * f x * (starRingEnd ℂ) (deriv g x)) := by
      intro x _
      simp only [map_mul, map_add, map_ofNat, map_div₀, map_one, Complex.conj_I,
        Complex.conj_ofReal]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
      integral_add ((hia.restrict).const_mul _) hid.restrict, integral_const_mul, hIa, hId]
  rw [hL, hR]
  linear_combination Complex.I * key


/-- **Symmetry of the Berry–Keating dilation generator on the smooth compactly supported core.**

For `f, g` smooth with compact support contained in `(0, ∞)`,
`∫ (A f) · conj g = ∫ f · conj (A g)` on `(0, ∞)`, where `A f = i ((1/2) f + x f')`.
Only symmetry on the core is claimed here, not self-adjointness.

The hypotheses `hgc`, `hfs`, `hgs` are stated as requested but are not needed for the proof:
the boundary term carries a factor `x`, so it vanishes at `0` regardless of the location of the
supports, and compact support of `f` alone makes all the integrands compactly supported. -/
theorem symmetric_on_core (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hfs : tsupport f ⊆ Set.Ioi 0) (hgs : tsupport g ⊆ Set.Ioi 0) :
    ∫ x in Set.Ioi (0:ℝ),
        (Complex.I * ((1/2) * f x + (x : ℂ) * deriv f x)) * starRingEnd ℂ (g x)
      = ∫ x in Set.Ioi (0:ℝ),
        f x * starRingEnd ℂ (Complex.I * ((1/2) * g x + (x : ℂ) * deriv g x)) :=
  symmetric_on_core_contDiff_one f g (hf.of_le le_top) (hg.of_le le_top) hfc

/-- The same symmetry statement for `C^∞` (rather than real-analytic) functions, which is the
usual meaning of the `C_c^∞(0, ∞)` core. -/
theorem symmetric_on_core_smooth (f g : ℝ → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hfs : tsupport f ⊆ Set.Ioi 0) (hgs : tsupport g ⊆ Set.Ioi 0) :
    ∫ x in Set.Ioi (0:ℝ),
        (Complex.I * ((1/2) * f x + (x : ℂ) * deriv f x)) * starRingEnd ℂ (g x)
      = ∫ x in Set.Ioi (0:ℝ),
        f x * starRingEnd ℂ (Complex.I * ((1/2) * g x + (x : ℂ) * deriv g x)) :=
  symmetric_on_core_contDiff_one f g (hf.of_le (by exact_mod_cast le_top))
    (hg.of_le (by exact_mod_cast le_top)) hfc

end DilationGenerator
end Brockian

