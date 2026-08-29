import Mathlib

/-!
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
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

open MeasureTheory

namespace Frontier

/-- Auxiliary: a differentiable function is continuous. -/

theorem abs_le_integral_abs_deriv {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hint : Integrable u') (hsupp : HasCompactSupport u) (x : ℝ) :
    |u x| ≤ ∫ y, |u' y| := by
  obtain ⟨a, hax, hua⟩ := exists_base_point hsupp x
  have key : ∫ y in a..x, u' y = u x - u a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hu y)
      hint.intervalIntegrable
  rw [hua, sub_zero] at key
  calc |u x| = |∫ y in a..x, u' y| := by rw [key]
    _ ≤ ∫ y in a..x, |u' y| := intervalIntegral.abs_integral_le_integral_abs hax
    _ ≤ ∫ y, |u' y| := by
        rw [intervalIntegral.integral_of_le hax]
        exact setIntegral_le_integral hint.abs
          (Filter.Eventually.of_forall fun y => abs_nonneg _)

/-- **The Gagliardo–Nirenberg interpolation inequality (one-dimensional base case).**
For a compactly supported continuously differentiable function `u : ℝ → ℝ` with derivative `u'`,
one has the pointwise interpolation bound
`u x ^ 2 ≤ 2 ‖u‖_{L²} ‖u'‖_{L²}`,
i.e. `‖u‖_∞ ≤ √2 · ‖u‖_{L²}^{1/2} · ‖u'‖_{L²}^{1/2}`. -/
