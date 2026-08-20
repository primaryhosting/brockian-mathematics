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

/-
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Complex
open scoped Convolution

namespace Brockian.Weyl.SchrodingerMinimal

/-! ## Test functions and the minimal Schrödinger expression -/

/-- A test function on the line: smooth with compact support. -/

theorem schrodinger_symmetric (V₀ : ℝ) {f g : ℝ → ℂ} (hf : IsTestFunction f)
    (hg : IsTestFunction g) :
    ∫ x, (starRingEnd ℂ) (schrodingerExpr V₀ f x) * g x
      = ∫ x, (starRingEnd ℂ) (f x) * schrodingerExpr V₀ g x := by
  obtain ⟨hfs, hfc⟩ := hf
  obtain ⟨hgs, hgc⟩ := hg
  have hfs' : ContDiff ℝ (⊤ : ℕ∞) (deriv f) := by simpa using hfs.iterate_deriv 1
  have hgs' : ContDiff ℝ (⊤ : ℕ∞) (deriv g) := by simpa using hgs.iterate_deriv 1
  have hfs'' : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv f)) := by simpa using hfs.iterate_deriv 2
  have hgs'' : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv g)) := by simpa using hgs.iterate_deriv 2
  have hf1 : Differentiable ℝ f := hfs.differentiable (by simp)
  have hg1 : Differentiable ℝ g := hgs.differentiable (by simp)
  have hf1' : Differentiable ℝ (deriv f) := hfs'.differentiable (by simp)
  have hg1' : Differentiable ℝ (deriv g) := hgs'.differentiable (by simp)
  have hconjf : HasCompactSupport (fun x => (starRingEnd ℂ) (f x)) :=
    hfc.comp_left (g := fun z : ℂ => (starRingEnd ℂ) z) (by simp)
  -- the boundary term `conj f' * g - conj f * g'` is a compactly supported `C¹` function
  set h : ℝ → ℂ := fun x => (starRingEnd ℂ) (deriv f x) * g x
      - (starRingEnd ℂ) (f x) * deriv g x with hh
  have hderiv : ∀ x, HasDerivAt h
      ((starRingEnd ℂ) (deriv (deriv f) x) * g x
        - (starRingEnd ℂ) (f x) * deriv (deriv g) x) x := by
    intro x
    have a1 : HasDerivAt (fun y => (starRingEnd ℂ) (deriv f y))
        ((starRingEnd ℂ) (deriv (deriv f) x)) x := ((hf1' x).hasDerivAt).star
    have a2 : HasDerivAt g (deriv g x) x := (hg1 x).hasDerivAt
    have a3 : HasDerivAt (fun y => (starRingEnd ℂ) (f y)) ((starRingEnd ℂ) (deriv f x)) x :=
      ((hf1 x).hasDerivAt).star
    have a4 : HasDerivAt (deriv g) (deriv (deriv g) x) x := (hg1' x).hasDerivAt
    have a5 := (a1.mul a2).sub (a3.mul a4)
    convert a5 using 1
    ring
  have hcont : ContDiff ℝ 1 h := by
    have c1 : ContDiff ℝ (⊤ : ℕ∞) (fun y => (starRingEnd ℂ) (deriv f y)) :=
      Complex.conjCLE.contDiff.comp hfs'
    have c2 : ContDiff ℝ (⊤ : ℕ∞) (fun y => (starRingEnd ℂ) (f y)) :=
      Complex.conjCLE.contDiff.comp hfs
    exact ((c1.mul hgs).sub (c2.mul hgs')).of_le (by exact_mod_cast le_top)
  have hcs : HasCompactSupport h := HasCompactSupport.sub hgc.mul_left hgc.deriv.mul_left
  have hzero : ∫ x, ((starRingEnd ℂ) (deriv (deriv f) x) * g x
      - (starRingEnd ℂ) (f x) * deriv (deriv g) x) = 0 := by
    have hd : deriv h = fun x => (starRingEnd ℂ) (deriv (deriv f) x) * g x
        - (starRingEnd ℂ) (f x) * deriv (deriv g) x := funext fun x => (hderiv x).deriv
    rw [← hd]
    exact integral_deriv_eq_zero hcont hcs
  have hint1 : Integrable (fun x => (starRingEnd ℂ) (schrodingerExpr V₀ f x) * g x) volume := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (Complex.continuous_conj.comp
        (hfs''.continuous.neg.add (continuous_const.mul hfs.continuous))).mul hg1.continuous
    · exact hgc.mul_left
  have hint2 : Integrable (fun x => (starRingEnd ℂ) (f x) * schrodingerExpr V₀ g x) volume := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (Complex.continuous_conj.comp hfs.continuous).mul
        (hgs''.continuous.neg.add (continuous_const.mul hgs.continuous))
    · exact hconjf.mul_right
  have hfinal : (∫ x, (starRingEnd ℂ) (schrodingerExpr V₀ f x) * g x)
      - ∫ x, (starRingEnd ℂ) (f x) * schrodingerExpr V₀ g x = 0 := by
    rw [← integral_sub hint1 hint2]
    have hcongr : (fun x => (starRingEnd ℂ) (schrodingerExpr V₀ f x) * g x
          - (starRingEnd ℂ) (f x) * schrodingerExpr V₀ g x)
        = fun x => -((starRingEnd ℂ) (deriv (deriv f) x) * g x
          - (starRingEnd ℂ) (f x) * deriv (deriv g) x) := by
      funext x
      simp only [schrodingerExpr, map_add, map_neg, map_mul, Complex.conj_ofReal]
      ring
    rw [hcongr, integral_neg, hzero, neg_zero]
  exact sub_eq_zero.mp hfinal

/-! ## The deficiency spaces are trivial -/

/-- **Main analytic step (the discharged ODE hypothesis).**
If `u ∈ L²(ℝ)` is orthogonal to the range of `τ - z` on test functions, with `z` non-real,
then `u = 0` almost everywhere. -/
