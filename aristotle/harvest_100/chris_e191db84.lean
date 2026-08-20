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

set_option grind.warning false

namespace Brockian
namespace DilationGenerator

open MeasureTheory Complex

/-- Auxiliary product `x ↦ x · f x · conj (g x)` whose derivative encodes the
integration-by-parts identity for the Berry–Keating dilation generator. -/
noncomputable def prodAux (f g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (x : ℂ) * f x * (starRingEnd ℂ) (g x)

lemma hasDerivAt_conj {g : ℝ → ℂ} {x : ℝ} (h : HasDerivAt g (deriv g x) x) :
    HasDerivAt (fun y => (starRingEnd ℂ) (g y)) ((starRingEnd ℂ) (deriv g x)) x := by
  simpa using (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x h)

lemma contDiff_conj {g : ℝ → ℂ} {n : ℕ∞} (h : ContDiff ℝ (n : WithTop ℕ∞) g) :
    ContDiff ℝ (n : WithTop ℕ∞) (fun y => (starRingEnd ℂ) (g y)) :=
  Complex.conjCLE.toContinuousLinearMap.contDiff.comp h

lemma hasDerivAt_prodAux {f g : ℝ → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (x : ℝ) :
    HasDerivAt (prodAux f g)
      (f x * (starRingEnd ℂ) (g x) + (x : ℂ) * deriv f x * (starRingEnd ℂ) (g x)
        + (x : ℂ) * f x * (starRingEnd ℂ) (deriv g x)) x := by
  have hx : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using Complex.ofRealCLM.hasDerivAt (x := x)
  have hfx : HasDerivAt f (deriv f x) x := (hf.differentiable (by simp) x).hasDerivAt
  have hgx : HasDerivAt g (deriv g x) x := (hg.differentiable (by simp) x).hasDerivAt
  have hcg := hasDerivAt_conj hgx
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) * f y) (1 * f x + (x : ℂ) * deriv f x) x :=
    hx.mul hfx
  have h2 := h1.mul hcg
  convert h2 using 1
  ring

lemma contDiff_prodAux {f g : ℝ → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) :
    ContDiff ℝ (1 : WithTop ℕ∞) (prodAux f g) := by
  have hx : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ => (y : ℂ)) :=
    Complex.ofRealCLM.contDiff
  have : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (prodAux f g) :=
    (hx.mul hf).mul (contDiff_conj hg)
  exact this.of_le (by exact_mod_cast le_top)

lemma hasCompactSupport_prodAux {f g : ℝ → ℂ} (hfc : HasCompactSupport f) :
    HasCompactSupport (prodAux f g) := by
  have : HasCompactSupport (fun x : ℝ => ((x : ℂ) * f x) * (starRingEnd ℂ) (g x)) :=
    (hfc.mul_left (f := fun x : ℝ => (x : ℂ))).mul_right
  exact this

lemma integral_deriv_prodAux {f g : ℝ → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hfc : HasCompactSupport f) :
    ∫ x in Set.Ioi (0 : ℝ), deriv (prodAux f g) x = 0 := by
  have := HasCompactSupport.integral_Ioi_deriv_eq (f := prodAux f g)
    (contDiff_prodAux hf hg) (hasCompactSupport_prodAux (g := g) hfc) 0
  simpa [prodAux] using this

/-- The Berry–Keating dilation generator `A f = i·((1/2)·f + x·f')` is symmetric on the
core of smooth compactly supported functions on `(0, ∞)`.

The hypotheses `tsupport f ⊆ Set.Ioi 0` and `tsupport g ⊆ Set.Ioi 0`, which are part of the
requested statement, are not needed for the proof (the boundary term at `0` vanishes because
of the factor `x`), but they are kept since they describe the intended core. -/
theorem symmetric_on_core (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (_hfs : tsupport f ⊆ Set.Ioi 0) (_hgs : tsupport g ⊆ Set.Ioi 0) :
    ∫ x in Set.Ioi (0 : ℝ),
        (Complex.I * ((1 / 2) * f x + (x : ℂ) * deriv f x)) * starRingEnd ℂ (g x)
      = ∫ x in Set.Ioi (0 : ℝ),
        f x * starRingEnd ℂ (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x)) := by
  set P : ℝ → ℂ := fun x =>
    (Complex.I * ((1 / 2) * f x + (x : ℂ) * deriv f x)) * starRingEnd ℂ (g x) with hP
  set Q : ℝ → ℂ := fun x =>
    f x * starRingEnd ℂ (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x)) with hQ
  have cf : Continuous f := hf.continuous
  have cg : Continuous g := hg.continuous
  have cdf : Continuous (deriv f) := hf.continuous_deriv (by simp)
  have cdg : Continuous (deriv g) := hg.continuous_deriv (by simp)
  have ccg : Continuous fun x : ℝ => starRingEnd ℂ (g x) := Complex.continuous_conj.comp cg
  have hcg : HasCompactSupport fun x : ℝ => starRingEnd ℂ (g x) :=
    hgc.comp_left (g := starRingEnd ℂ) (map_zero _)
  have cP : Continuous P := by
    have : Continuous fun x : ℝ => Complex.I * ((1 / 2) * f x + (x : ℂ) * deriv f x) :=
      continuous_const.mul ((continuous_const.mul cf).add (Complex.continuous_ofReal.mul cdf))
    exact this.mul ccg
  have cQ : Continuous Q := by
    have : Continuous fun x : ℝ =>
        starRingEnd ℂ (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x)) :=
      Complex.continuous_conj.comp
        (continuous_const.mul ((continuous_const.mul cg).add (Complex.continuous_ofReal.mul cdg)))
    exact cf.mul this
  have sP : HasCompactSupport P := hcg.mul_left
  have sQ : HasCompactSupport Q := hfc.mul_right
  have iP : IntegrableOn P (Set.Ioi (0 : ℝ)) :=
    (cP.integrable_of_hasCompactSupport sP).integrableOn
  have iQ : IntegrableOn Q (Set.Ioi (0 : ℝ)) :=
    (cQ.integrable_of_hasCompactSupport sQ).integrableOn
  have hkey : ∀ x : ℝ, P x - Q x = Complex.I * deriv (prodAux f g) x := by
    intro x
    rw [(hasDerivAt_prodAux hf hg x).deriv]
    simp only [hP, hQ, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_div₀, map_one,
      map_ofNat]
    ring
  have hzero : ∫ x in Set.Ioi (0 : ℝ), (P x - Q x) = 0 := by
    have : ∫ x in Set.Ioi (0 : ℝ), (P x - Q x)
        = ∫ x in Set.Ioi (0 : ℝ), Complex.I * deriv (prodAux f g) x := by
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x _ => hkey x
    rw [this, MeasureTheory.integral_const_mul, integral_deriv_prodAux hf hg hfc, mul_zero]
  rw [MeasureTheory.integral_sub iP iQ] at hzero
  exact sub_eq_zero.mp hzero

end DilationGenerator
end Brockian

