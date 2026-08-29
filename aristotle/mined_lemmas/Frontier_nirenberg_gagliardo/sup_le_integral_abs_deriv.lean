/-
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
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

namespace Frontier

open MeasureTheory

/-- A compactly supported function on `ℝ` vanishes at some point to the left of any given point. -/

theorem sup_le_integral_abs_deriv {u u' : ℝ → ℝ}
    (hderiv : ∀ x : ℝ, HasDerivAt u (u' x) x) (hsupp : HasCompactSupport u)
    (hu' : Integrable u' volume) (x : ℝ) :
    |u x| ≤ ∫ t : ℝ, |u' t| := by
  obtain ⟨a, hax, hua⟩ := exists_le_apply_eq_zero hsupp x
  have hftc : (∫ y : ℝ in a..x, u' y) = u x - u a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y)
      (hu'.intervalIntegrable a x)
  rw [hua, sub_zero] at hftc
  calc |u x| = |∫ y : ℝ in a..x, u' y| := by rw [hftc]
    _ ≤ ∫ y : ℝ in a..x, |u' y| := intervalIntegral.abs_integral_le_integral_abs hax
    _ = ∫ y : ℝ in Set.Ioc a x, |u' y| := intervalIntegral.integral_of_le hax
    _ ≤ ∫ t : ℝ, |u' t| :=
        setIntegral_le_integral hu'.abs (Filter.Eventually.of_forall fun t => abs_nonneg _)

/-- **Gagliardo–Nirenberg interpolation inequality** (one-dimensional base case).

For a compactly supported continuously differentiable function `u : ℝ → ℝ`, the `L^∞` norm is
controlled by the geometric mean of the `L²` norms of `u` and of its derivative:
`‖u‖_∞ ^ 2 ≤ 2 ‖u‖_{L²} ‖u'‖_{L²}`. -/
