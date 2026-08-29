/-
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory

set_option autoImplicit false

namespace Frontier

/--
**Gagliardo–Nirenberg (base case, `n = 1`, `p = 1`).**

If `u : ℝ → ℝ` is everywhere differentiable with derivative `u'`, `u'` is integrable, and `u`
has compact support, then

`‖u‖_{L^∞} ≤ (1/2) * ‖u'‖_{L^1}`,

pointwise: `|u x| ≤ (1/2) * ∫ t, |u' t|` for every `x`.

This is the one-dimensional endpoint case of the Gagliardo–Nirenberg–Sobolev inequality: it is
obtained by writing `u x` both as `∫_{-S}^{x} u'` and as `-∫_{x}^{S} u'` (where `[-S, S]` contains
the support of `u`), and adding the two resulting bounds.  The constant `1/2` is sharp.
-/

theorem nirenberg_gagliardo_sq
    {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Integrable u')
    (hsupp : HasCompactSupport u) (x : ℝ) :
    |u x| ^ 2 ≤ ∫ t, |u t| * |u' t| := by
  have hcont : Continuous u := continuous_iff_continuousAt.mpr fun y => (hu y).continuousAt
  obtain ⟨C, hC⟩ := hsupp.exists_bound_of_continuous hcont
  have hmul : Integrable (fun t => 2 * u t * u' t) := by
    have h : Integrable (fun t => (2 * u t) * u' t) :=
      hu'.bdd_mul (c := 2 * C) (by fun_prop)
        (Filter.Eventually.of_forall fun t => by
          have h1 : |u t| ≤ C := by simpa using hC t
          rw [Real.norm_eq_abs, abs_mul, abs_two]
          linarith)
    simpa [mul_assoc] using h
  have hd : ∀ y, HasDerivAt (fun z => u z * u z) (2 * u y * u' y) y := by
    intro y
    have h := (hu y).mul (hu y)
    convert h using 1
    ring
  have hsupp2 : HasCompactSupport (fun z => u z * u z) := hsupp.mul_right
  have key := nirenberg_gagliardo hd hmul hsupp2 x
  have heq : (fun t => |2 * u t * u' t|) = fun t => 2 * (|u t| * |u' t|) := by
    funext t
    rw [abs_mul, abs_mul, abs_two]
    ring
  rw [heq, integral_const_mul] at key
  calc |u x| ^ 2 = |u x * u x| := by rw [abs_mul]; ring
    _ ≤ 1 / 2 * (2 * ∫ t, |u t| * |u' t|) := key
    _ = ∫ t, |u t| * |u' t| := by ring

/-- Cauchy–Schwarz inequality for Bochner integrals of real functions. -/
