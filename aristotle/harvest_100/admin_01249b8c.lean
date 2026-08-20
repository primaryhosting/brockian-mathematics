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

/-- The pointwise product `x ↦ x · f x · conj (g x)`, whose derivative encodes the
integration-by-parts identity for the Berry–Keating dilation generator. -/
noncomputable def pairing (f g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (x : ℂ) * (f x * starRingEnd ℂ (g x))

/-- Conjugation `ℂ → ℂ` is smooth as a map of real normed spaces. -/
theorem contDiff_conj : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => starRingEnd ℂ z) := by
  simpa using (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.contDiff (n := (⊤ : ℕ∞))

/-- The derivative of `pairing f g`, computed by the product rule. -/
theorem hasDerivAt_pairing {f g : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : ℝ) :
    HasDerivAt (pairing f g)
      (f x * starRingEnd ℂ (g x) +
        (x : ℂ) * (deriv f x * starRingEnd ℂ (g x) +
          f x * starRingEnd ℂ (deriv g x))) x := by
  have hx : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x))
  have hfd : HasDerivAt f (deriv f x) x :=
    (hf.differentiable (by norm_num) x).hasDerivAt
  have hgd : HasDerivAt g (deriv g x) x :=
    (hg.differentiable (by norm_num) x).hasDerivAt
  have hgs : HasDerivAt (fun t : ℝ => starRingEnd ℂ (g t)) (starRingEnd ℂ (deriv g x)) x := by
    simpa [Complex.star_def] using hgd.star
  have := hx.mul (hfd.mul hgs)
  simpa [pairing, one_mul] using this

/-- `pairing f g` is `C^1`. -/
theorem contDiff_pairing {f g : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : ContDiff ℝ 1 (pairing f g) := by
  have hconj : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => starRingEnd ℂ (g x)) :=
    contDiff_conj.comp hg
  have hx : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (x : ℂ)) :=
    Complex.ofRealCLM.contDiff
  exact ((hx.mul (hf.mul hconj)).of_le (by exact_mod_cast le_top))

/-- `pairing f g` has compact support as soon as `f` does. -/
theorem hasCompactSupport_pairing {f g : ℝ → ℂ} (hfc : HasCompactSupport f) :
    HasCompactSupport (pairing f g) := by
  have h1 : HasCompactSupport (fun x : ℝ => f x * starRingEnd ℂ (g x)) :=
    hfc.mul_right
  exact h1.mul_left

/-- The integral over `(0, ∞)` of the derivative of `pairing f g` vanishes: the boundary
term at `0` is killed by the factor `x`, and the one at `+∞` by compact support. -/
theorem integral_deriv_pairing {f g : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hfc : HasCompactSupport f) :
    ∫ x in Set.Ioi (0 : ℝ), deriv (pairing f g) x = 0 := by
  have := HasCompactSupport.integral_Ioi_deriv_eq (contDiff_pairing hf hg)
    (hasCompactSupport_pairing (f := f) (g := g) hfc) 0
  simpa [pairing] using this

/-- **Symmetry of the Berry–Keating dilation generator on the smooth compactly supported
core of `(0, ∞)`.**

For `f, g : ℝ → ℂ` smooth with compact support contained in `(0, ∞)`,
`∫ (A f) · conj g = ∫ f · conj (A g)` over `(0, ∞)`, where `A f = i·((1/2)·f + x·f')`.

This is symmetry on the core only; no self-adjointness statement is claimed.

The proof is integration by parts: the integrand difference is exactly
`i · d/dx (x · f · conj g)`, whose integral over `(0, ∞)` vanishes (the boundary term at `0`
vanishes because of the factor `x`, and at `+∞` by compact support). In particular the
hypotheses `HasCompactSupport g`, `tsupport f ⊆ Set.Ioi 0` and `tsupport g ⊆ Set.Ioi 0`,
which are part of the requested statement, turn out not to be needed. -/
theorem symmetric_on_core (f g : ℝ → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hfs : tsupport f ⊆ Set.Ioi 0) (hgs : tsupport g ⊆ Set.Ioi 0) :
    ∫ x in Set.Ioi (0 : ℝ),
        (Complex.I * ((1 / 2) * f x + (x : ℂ) * deriv f x)) * starRingEnd ℂ (g x)
      = ∫ x in Set.Ioi (0 : ℝ),
        f x * starRingEnd ℂ (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x)) := by
  classical
  set Q : ℝ → ℂ := fun x =>
    f x * starRingEnd ℂ (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x)) with hQdef
  set D : ℝ → ℂ := fun x => Complex.I * deriv (pairing f g) x with hDdef
  -- pointwise identity
  have hpt : ∀ x : ℝ,
      (Complex.I * ((1 / 2) * f x + (x : ℂ) * deriv f x)) * starRingEnd ℂ (g x)
        = Q x + D x := by
    intro x
    have hd : deriv (pairing f g) x =
        f x * starRingEnd ℂ (g x) +
          (x : ℂ) * (deriv f x * starRingEnd ℂ (g x) +
            f x * starRingEnd ℂ (deriv g x)) :=
      (hasDerivAt_pairing hf hg x).deriv
    simp only [hQdef, hDdef, hd, map_mul, map_add, map_div₀, map_one, map_ofNat,
      Complex.conj_I, Complex.conj_ofReal]
    ring
  -- integrability of the two pieces
  have hcontf : Continuous f := hf.continuous
  have hcontg : Continuous g := hg.continuous
  have hcontdg : Continuous (deriv g) := hg.continuous_deriv (by exact_mod_cast le_top)
  have hcontQ : Continuous Q := by
    fun_prop
  have hQcs : HasCompactSupport Q := by
    apply HasCompactSupport.intro hfc
    intro x hx
    have : f x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [hQdef, this]
  have hDcont : Continuous D := by
    have : Continuous (deriv (pairing f g)) :=
      (contDiff_pairing hf hg).continuous_deriv (by norm_num)
    exact continuous_const.mul this
  have hDcs : HasCompactSupport D := by
    have h := (hasCompactSupport_pairing (f := f) (g := g) hfc).deriv
    exact h.mul_left
  have hQint : MeasureTheory.IntegrableOn Q (Set.Ioi (0 : ℝ)) :=
    (hcontQ.integrable_of_hasCompactSupport hQcs).integrableOn
  have hDint : MeasureTheory.IntegrableOn D (Set.Ioi (0 : ℝ)) :=
    (hDcont.integrable_of_hasCompactSupport hDcs).integrableOn
  calc ∫ x in Set.Ioi (0 : ℝ),
        (Complex.I * ((1 / 2) * f x + (x : ℂ) * deriv f x)) * starRingEnd ℂ (g x)
      = ∫ x in Set.Ioi (0 : ℝ), (Q x + D x) := by
        exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x _ => hpt x)
    _ = (∫ x in Set.Ioi (0 : ℝ), Q x) + ∫ x in Set.Ioi (0 : ℝ), D x :=
        MeasureTheory.integral_add hQint hDint
    _ = ∫ x in Set.Ioi (0 : ℝ), Q x := by
        have : ∫ x in Set.Ioi (0 : ℝ), D x = 0 := by
          rw [hDdef]
          rw [MeasureTheory.integral_const_mul, integral_deriv_pairing hf hg hfc, mul_zero]
        rw [this, add_zero]

end DilationGenerator
end Brockian

#print axioms Brockian.DilationGenerator.symmetric_on_core

