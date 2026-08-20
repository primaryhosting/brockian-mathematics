import Mathlib
/-!
# Symmetric On Core
Category: Gate1 Operator
Target: Brockian.DilationGenerator.symmetric_on_core
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Complex

namespace Brockian
namespace DilationGenerator

variable {f g : ℝ → ℂ}

/-- The bilinear "boundary weight" `x ↦ x * f x * conj (g x)`, whose derivative is exactly the
combination of terms appearing in the difference of the two sides of the symmetry identity. -/
noncomputable def weight (f g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (x : ℂ) * f x * (starRingEnd ℂ) (g x)

lemma weight_contDiff (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 (weight f g) :=
  (Complex.ofRealCLM.contDiff.mul hf).mul
    (((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff).comp hg)

lemma weight_hasCompactSupport (hg : HasCompactSupport g) :
    HasCompactSupport (weight f g) := by
  have h : HasCompactSupport (fun x : ℝ => (starRingEnd ℂ) (g x)) :=
    hg.comp_left (g := starRingEnd ℂ) (map_zero _)
  exact HasCompactSupport.mul_left (f := fun x : ℝ => (x : ℂ) * f x) h

lemma deriv_weight (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (x : ℝ) :
    deriv (weight f g) x =
      f x * (starRingEnd ℂ) (g x) + (x : ℂ) * deriv f x * (starRingEnd ℂ) (g x)
        + (x : ℂ) * f x * (starRingEnd ℂ) (deriv g x) := by
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt f (deriv f x) x :=
    (hf.differentiable (by norm_num) x).hasDerivAt
  have h3 : HasDerivAt (fun y : ℝ => (starRingEnd ℂ) (g y)) ((starRingEnd ℂ) (deriv g x)) x := by
    simpa using ((hg.differentiable (by norm_num) x).hasDerivAt).star
  have hd : HasDerivAt (fun y : ℝ => (y : ℂ) * f y * (starRingEnd ℂ) (g y))
      ((1 * f x + (x : ℂ) * deriv f x) * (starRingEnd ℂ) (g x)
        + (x : ℂ) * f x * (starRingEnd ℂ) (deriv g x)) x := (h1.mul h2).mul h3
  have hw : weight f g = fun y : ℝ => (y : ℂ) * f y * (starRingEnd ℂ) (g y) := rfl
  rw [hw, hd.deriv]
  ring

/-- The integral over `(0, ∞)` of the derivative of the boundary weight vanishes: the weight is
`C^1` with compact support and vanishes at `0`. -/
lemma integral_deriv_weight_Ioi (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hg' : HasCompactSupport g) :
    ∫ x in Set.Ioi (0 : ℝ), deriv (weight f g) x = 0 := by
  rw [HasCompactSupport.integral_Ioi_deriv_eq (weight_contDiff hf hg)
    (weight_hasCompactSupport hg') 0]
  simp [weight]

/-- **Symmetry of the Berry–Keating dilation generator on the core `C_c^∞(0, ∞)`.**

For `f, g` smooth with compact support contained in `(0, ∞)`,
`∫ (A f) * conj g = ∫ f * conj (A g)` over `(0, ∞)`, where `A h = i * ((1/2) h + x h')`.

This is symmetry only; no self-adjointness claim is made.

Remark on hypotheses: the proof shows that the compact-support hypotheses alone suffice — the
requirement `tsupport f ⊆ Set.Ioi 0` (and likewise for `g`) is retained because it is part of the
requested statement, but it is not needed, since the boundary term `x * f x * conj (g x)` vanishes
at `x = 0` for trivial reasons. -/
theorem symmetric_on_core (f g : ℝ → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hfs : tsupport f ⊆ Set.Ioi (0 : ℝ)) (hgs : tsupport g ⊆ Set.Ioi (0 : ℝ)) :
    ∫ x in Set.Ioi (0 : ℝ),
        (Complex.I * ((1 / 2) * f x + (x : ℂ) * deriv f x)) * starRingEnd ℂ (g x) =
      ∫ x in Set.Ioi (0 : ℝ),
        f x * starRingEnd ℂ (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x)) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le ENat.LEInfty.out
  have hg1 : ContDiff ℝ 1 g := hg.of_le ENat.LEInfty.out
  have hf2 : ContDiff ℝ 2 f := hf.of_le ENat.LEInfty.out
  have hg2 : ContDiff ℝ 2 g := hg.of_le ENat.LEInfty.out
  -- continuity of the derivatives
  have hdf : Continuous (deriv f) := hf2.continuous_deriv (by norm_num)
  have hdg : Continuous (deriv g) := hg2.continuous_deriv (by norm_num)
  have hcf : Continuous f := hf1.continuous
  have hcg : Continuous g := hg1.continuous
  -- the two integrands
  set F : ℝ → ℂ := fun x =>
    (Complex.I * ((1 / 2) * f x + (x : ℂ) * deriv f x)) * starRingEnd ℂ (g x) with hF
  set G : ℝ → ℂ := fun x =>
    f x * starRingEnd ℂ (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x)) with hG
  have hFcont : Continuous F := by
    rw [hF]; fun_prop
  have hGcont : Continuous G := by
    rw [hG]; fun_prop
  have hFsupp : HasCompactSupport F := by
    have h : HasCompactSupport (fun x : ℝ => (starRingEnd ℂ) (g x)) :=
      hgc.comp_left (g := starRingEnd ℂ) (map_zero _)
    exact HasCompactSupport.mul_left
      (f := fun x : ℝ => Complex.I * ((1 / 2) * f x + (x : ℂ) * deriv f x)) h
  have hGsupp : HasCompactSupport G :=
    HasCompactSupport.mul_right (f := f)
      (f' := fun x : ℝ => starRingEnd ℂ (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x))) hfc
  have hFint : IntegrableOn F (Set.Ioi (0 : ℝ)) :=
    (hFcont.integrable_of_hasCompactSupport hFsupp).integrableOn
  have hGint : IntegrableOn G (Set.Ioi (0 : ℝ)) :=
    (hGcont.integrable_of_hasCompactSupport hGsupp).integrableOn
  have hsub : (∫ x in Set.Ioi (0 : ℝ), F x) - ∫ x in Set.Ioi (0 : ℝ), G x
      = ∫ x in Set.Ioi (0 : ℝ), Complex.I * deriv (weight f g) x := by
    rw [← integral_sub hFint hGint]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    rw [deriv_weight hf1 hg1 x, hF, hG]
    simp only [map_mul, map_add, map_ofNat, Complex.conj_I, map_div₀, map_one,
      Complex.conj_ofReal]
    ring
  have hzero : ∫ x in Set.Ioi (0 : ℝ), Complex.I * deriv (weight f g) x = 0 := by
    rw [integral_const_mul, integral_deriv_weight_Ioi hf1 hg1 hgc, mul_zero]
  exact sub_eq_zero.mp (hsub.trans hzero)

end DilationGenerator
end Brockian

#print axioms Brockian.DilationGenerator.symmetric_on_core

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

