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

open MeasureTheory

/-- The auxiliary function `x ↦ x · f(x) · conj(g(x))`, whose derivative is exactly the
integrand appearing in the difference of the two sides of the symmetry identity. -/
noncomputable def pairing (f g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (x : ℂ) * f x * (starRingEnd ℂ) (g x)

theorem hasDerivAt_pairing {f g : ℝ → ℂ} {x : ℝ}
    (hf : HasDerivAt f (deriv f x) x) (hg : HasDerivAt g (deriv g x) x) :
    HasDerivAt (pairing f g)
      ((1 * f x + (x : ℂ) * deriv f x) * (starRingEnd ℂ) (g x)
        + ((x : ℂ) * f x) * (starRingEnd ℂ) (deriv g x)) x := by
  have hx : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
    simpa using Complex.ofRealCLM.hasDerivAt (x := x)
  exact (hx.mul hf).mul hg.star

theorem contDiff_pairing {f g : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : ContDiff ℝ 1 (pairing f g) := by
  have hcg : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (starRingEnd ℂ) (g x)) :=
    Complex.conjCLE.contDiff.comp hg
  have hx : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (t : ℂ)) :=
    Complex.ofRealCLM.contDiff.of_le le_top
  exact (((hx.mul hf).mul hcg).of_le (by exact_mod_cast le_top))

theorem hasCompactSupport_pairing {f g : ℝ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (pairing f g) := by
  refine HasCompactSupport.intro hf (fun x hx => ?_)
  simp [pairing, image_eq_zero_of_notMem_tsupport hx]

/-- **Symmetry of the Berry–Keating dilation generator on the smooth compactly supported
core of `(0, ∞)`.**

For `f, g` smooth with compact support contained in `(0, ∞)`, the operator
`A f = i · ((1/2) f + x f')` satisfies `⟪A f, g⟫ = ⟪f, A g⟫`, i.e.

`∫_{(0,∞)} (A f)(x) · conj (g x) = ∫_{(0,∞)} f x · conj ((A g)(x))`.

The proof is integration by parts: the difference of the two integrands equals
`i · d/dx (x · f(x) · conj(g(x)))`, and the integral of this exact derivative over `(0, ∞)`
vanishes because the primitive is compactly supported and vanishes at `0`.

This is symmetry on the core only; no self-adjointness claim is made.

Note: the support hypotheses `tsupport f ⊆ (0,∞)` and `tsupport g ⊆ (0,∞)` are kept because
they are part of the requested statement, but the proof does not need them (the boundary term
at `0` vanishes automatically since the primitive carries a factor of `x`). -/
theorem symmetric_on_core (f g : ℝ → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (_hfs : tsupport f ⊆ Set.Ioi 0) (_hgs : tsupport g ⊆ Set.Ioi 0) :
    ∫ x in Set.Ioi (0 : ℝ),
        (Complex.I * ((1 / 2) * f x + (x : ℂ) * deriv f x)) * (starRingEnd ℂ) (g x)
      = ∫ x in Set.Ioi (0 : ℝ),
        f x * (starRingEnd ℂ) (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x)) := by
  -- Derivatives exist everywhere.
  have hfd : ∀ x : ℝ, HasDerivAt f (deriv f x) x := fun x =>
    (hf.differentiable (by exact_mod_cast le_top) x).hasDerivAt
  have hgd : ∀ x : ℝ, HasDerivAt g (deriv g x) x := fun x =>
    (hg.differentiable (by exact_mod_cast le_top) x).hasDerivAt
  -- Continuity facts.
  have hfC : Continuous f := hf.continuous
  have hgC : Continuous g := hg.continuous
  have hfdC : Continuous (deriv f) := by
    have := (hf.iterate_deriv' 0 1).continuous
    simpa using ((hf.deriv_right (m := (⊤ : ℕ∞)) (by exact_mod_cast le_top)).continuous)
  have hgdC : Continuous (deriv g) := by
    simpa using ((hg.deriv_right (m := (⊤ : ℕ∞)) (by exact_mod_cast le_top)).continuous)
  -- The primitive.
  have hP1 : ContDiff ℝ 1 (pairing f g) := contDiff_pairing hf hg
  have hPc : HasCompactSupport (pairing f g) := hasCompactSupport_pairing hfc
  -- Its derivative.
  have hPderiv : ∀ x : ℝ, deriv (pairing f g) x =
      (1 * f x + (x : ℂ) * deriv f x) * (starRingEnd ℂ) (g x)
        + ((x : ℂ) * f x) * (starRingEnd ℂ) (deriv g x) := fun x =>
    (hasDerivAt_pairing (hfd x) (hgd x)).deriv
  -- The integral of the exact derivative vanishes.
  have hzero : ∫ x in Set.Ioi (0 : ℝ), Complex.I * deriv (pairing f g) x = 0 := by
    rw [MeasureTheory.integral_const_mul, hP1.integral_Ioi_deriv_eq hPc 0]
    simp [pairing]
  -- Pointwise identity.
  have hpoint : ∀ x : ℝ,
      (Complex.I * ((1 / 2) * f x + (x : ℂ) * deriv f x)) * (starRingEnd ℂ) (g x)
        = f x * (starRingEnd ℂ) (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x))
          + Complex.I * deriv (pairing f g) x := by
    intro x
    rw [hPderiv x]
    simp only [map_add, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_I,
      Complex.conj_ofReal]
    ring
  -- Integrability of the right-hand integrand.
  have hRHSc : Continuous fun x : ℝ =>
      f x * (starRingEnd ℂ) (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x)) := by
    fun_prop
  have hRHSs : HasCompactSupport fun x : ℝ =>
      f x * (starRingEnd ℂ) (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x)) := by
    refine HasCompactSupport.intro hfc (fun x hx => ?_)
    simp [image_eq_zero_of_notMem_tsupport hx]
  have hRHSint : IntegrableOn
      (fun x : ℝ => f x * (starRingEnd ℂ) (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x)))
      (Set.Ioi (0 : ℝ)) :=
    (hRHSc.integrable_of_hasCompactSupport hRHSs).restrict
  -- Integrability of the derivative term.
  have hDc : Continuous fun x : ℝ => Complex.I * deriv (pairing f g) x :=
    continuous_const.mul (hP1.continuous_deriv le_rfl)
  have hDs : HasCompactSupport fun x : ℝ => Complex.I * deriv (pairing f g) x :=
    (hPc.deriv).mul_left
  have hDint : IntegrableOn (fun x : ℝ => Complex.I * deriv (pairing f g) x)
      (Set.Ioi (0 : ℝ)) :=
    (hDc.integrable_of_hasCompactSupport hDs).restrict
  calc ∫ x in Set.Ioi (0 : ℝ),
        (Complex.I * ((1 / 2) * f x + (x : ℂ) * deriv f x)) * (starRingEnd ℂ) (g x)
      = ∫ x in Set.Ioi (0 : ℝ),
        (f x * (starRingEnd ℂ) (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x))
          + Complex.I * deriv (pairing f g) x) := by
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = (∫ x in Set.Ioi (0 : ℝ),
          f x * (starRingEnd ℂ) (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x)))
        + ∫ x in Set.Ioi (0 : ℝ), Complex.I * deriv (pairing f g) x :=
        MeasureTheory.integral_add hRHSint hDint
    _ = ∫ x in Set.Ioi (0 : ℝ),
          f x * (starRingEnd ℂ) (Complex.I * ((1 / 2) * g x + (x : ℂ) * deriv g x)) := by
        rw [hzero, add_zero]

end DilationGenerator
end Brockian

