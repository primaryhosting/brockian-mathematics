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
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.DilationGenerator

/-- Conjugation of a `C^1` function is `C^1`. -/
lemma contDiff_conj {g : ℝ → ℂ} {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (fun x => starRingEnd ℂ (g x)) :=
  Complex.conjCLE.toContinuousLinearMap.contDiff.comp hg

/-- Derivative of the conjugate of a complex-valued function of a real variable. -/
lemma hasDerivAt_conj {g : ℝ → ℂ} {g' : ℂ} {x : ℝ} (hg : HasDerivAt g g' x) :
    HasDerivAt (fun x => starRingEnd ℂ (g x)) (starRingEnd ℂ g') x := by
  simpa [Complex.star_def] using hg.star

/-- The Berry–Keating dilation generator `A f = i ((1/2) f + x f')` is symmetric on the
core of smooth compactly supported functions with support in `(0, ∞)`:
`∫_{(0,∞)} (A f) * conj g = ∫_{(0,∞)} f * conj (A g)`.

The proof is integration by parts: with `F x = x * f x * conj (g x)`, the difference of the
two integrands is `i * F'`, and `∫_{(0,∞)} F' = -F 0 = 0` since `F` is `C^1` with compact
support.  (Only compact support of `f` is needed; the hypotheses `hgc`, `hfs`, `hgs` are
kept as requested but turn out to be unnecessary, the boundary term at `0` vanishing
because of the factor `x`.) -/
theorem symmetric_on_core
    (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hfs : tsupport f ⊆ Set.Ioi 0) (hgs : tsupport g ⊆ Set.Ioi 0) :
    ∫ x in Set.Ioi (0:ℝ),
        (Complex.I * ((1/2) * f x + (x : ℂ) * deriv f x)) * starRingEnd ℂ (g x)
      = ∫ x in Set.Ioi (0:ℝ),
        f x * starRingEnd ℂ (Complex.I * ((1/2) * g x + (x : ℂ) * deriv g x)) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le le_top
  have hg1 : ContDiff ℝ 1 g := hg.of_le le_top
  have hfd : ∀ x, HasDerivAt f (deriv f x) x := fun x =>
    (hf1.differentiable (by norm_num) x).hasDerivAt
  have hgd : ∀ x, HasDerivAt g (deriv g x) x := fun x =>
    (hg1.differentiable (by norm_num) x).hasDerivAt
  set G : ℝ → ℂ := fun x => starRingEnd ℂ (g x) with hGdef
  have hGd : ∀ x, HasDerivAt G (starRingEnd ℂ (deriv g x)) x := fun x =>
    hasDerivAt_conj (hgd x)
  set F : ℝ → ℂ := fun x => (x : ℂ) * f x * G x with hFdef
  -- derivative of `F`
  have hcoe : ∀ x : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := fun x => by
    simpa using (hasDerivAt_id x).ofReal_comp
  have hFd : ∀ x : ℝ, HasDerivAt F
      (f x * G x + (x : ℂ) * (deriv f x * G x + f x * starRingEnd ℂ (deriv g x))) x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * f t) (1 * f x + (x : ℂ) * deriv f x) x :=
      (hcoe x).mul (hfd x)
    have h2 := h1.mul (hGd x)
    convert h2 using 1
    ring
  -- smoothness and compact support of `F`
  have hF1 : ContDiff ℝ 1 F := by
    have : ContDiff ℝ 1 (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
    exact (this.mul hf1).mul (contDiff_conj hg1)
  have hFc : HasCompactSupport F := by
    have h1 : HasCompactSupport (fun t : ℝ => (t : ℂ) * f t) := hfc.mul_left
    exact h1.mul_right
  have hF0 : F 0 = 0 := by simp [hFdef]
  have key : ∫ x in Set.Ioi (0:ℝ), deriv F x = 0 := by
    rw [HasCompactSupport.integral_Ioi_deriv_eq hF1 hFc 0, hF0, neg_zero]
  -- pointwise identity
  have hpoint : ∀ x : ℝ,
      (Complex.I * ((1/2) * f x + (x : ℂ) * deriv f x)) * starRingEnd ℂ (g x)
        = f x * starRingEnd ℂ (Complex.I * ((1/2) * g x + (x : ℂ) * deriv g x))
          + Complex.I * deriv F x := by
    intro x
    rw [(hFd x).deriv]
    simp only [map_add, map_mul, Complex.conj_I, map_div₀, map_one, map_ofNat,
      Complex.conj_ofReal, hGdef]
    ring
  -- integrability facts
  have hcf : Continuous f := hf1.continuous
  have hcg : Continuous g := hg1.continuous
  have hcdf : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hcdg : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  have hRcont : Continuous fun x : ℝ =>
      f x * starRingEnd ℂ (Complex.I * ((1/2) * g x + (x : ℂ) * deriv g x)) := by
    fun_prop
  have hRcs : HasCompactSupport fun x : ℝ =>
      f x * starRingEnd ℂ (Complex.I * ((1/2) * g x + (x : ℂ) * deriv g x)) :=
    hfc.mul_right
  have hRint : MeasureTheory.IntegrableOn
      (fun x : ℝ => f x * starRingEnd ℂ (Complex.I * ((1/2) * g x + (x : ℂ) * deriv g x)))
      (Set.Ioi (0:ℝ)) :=
    (hRcont.integrable_of_hasCompactSupport hRcs).integrableOn
  have hDint : MeasureTheory.IntegrableOn (fun x : ℝ => Complex.I * deriv F x)
      (Set.Ioi (0:ℝ)) := by
    have hc : Continuous (deriv F) := hF1.continuous_deriv (by norm_num)
    have hcs : HasCompactSupport (deriv F) := hFc.deriv
    exact (((continuous_const.mul hc)).integrable_of_hasCompactSupport
      hcs.mul_left).integrableOn
  calc ∫ x in Set.Ioi (0:ℝ),
        (Complex.I * ((1/2) * f x + (x : ℂ) * deriv f x)) * starRingEnd ℂ (g x)
      = ∫ x in Set.Ioi (0:ℝ),
        (f x * starRingEnd ℂ (Complex.I * ((1/2) * g x + (x : ℂ) * deriv g x))
          + Complex.I * deriv F x) := by
        exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x _ => hpoint x
    _ = (∫ x in Set.Ioi (0:ℝ),
          f x * starRingEnd ℂ (Complex.I * ((1/2) * g x + (x : ℂ) * deriv g x)))
        + ∫ x in Set.Ioi (0:ℝ), Complex.I * deriv F x :=
        MeasureTheory.integral_add hRint hDint
    _ = ∫ x in Set.Ioi (0:ℝ),
          f x * starRingEnd ℂ (Complex.I * ((1/2) * g x + (x : ℂ) * deriv g x)) := by
        rw [MeasureTheory.integral_const_mul, key, mul_zero, add_zero]

end Brockian.DilationGenerator

