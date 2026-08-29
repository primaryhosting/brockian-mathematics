/-
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module docstring `/-! ... -/` before `import`; the header above is
-- therefore a plain block comment, and is repeated verbatim as a module docstring below.)

import Mathlib

/-!
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
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

namespace Frontier

open Real intervalIntegral

/-! ## Vector algebra in `ℝ³`

We use `ℝ × ℝ × ℝ` as a model of `ℝ³` together with explicitly defined dot product,
cross product and Euclidean norm.  (The ambient `Prod` norm of Mathlib is the sup norm,
so we never use `‖·‖`; note that the notion of (Fréchet/one-variable) derivative does
not depend on the choice of an equivalent norm, so `deriv` below is the usual derivative
of an `ℝ³`-valued function.) -/

/-- Euclidean dot product on `ℝ³`. -/

lemma inner_integral_eq {R r : ℝ} (hr : 0 < r) (hR : r < R) (v : ℝ) :
    (∫ u in (0:ℝ)..(2 * π), meanCurv R r u v ^ 2 * areaElt R r u v)
      = π * R ^ 2 / (2 * r * Real.sqrt (R ^ 2 - r ^ 2)) := by
  have hs := sqrt_sub_pos hr hR
  rw [intervalIntegral.integral_congr
      (g := fun u => cos u + R ^ 2 / (4 * r) * (1 / (R + r * cos u)))
      (fun u _ => willmore_integrand_eq hr hR u v)]
  have hi1 : IntervalIntegrable (fun u : ℝ => cos u) MeasureTheory.volume 0 (2 * π) :=
    Real.continuous_cos.intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun u : ℝ => R ^ 2 / (4 * r) * (1 / (R + r * cos u)))
      MeasureTheory.volume 0 (2 * π) :=
    (continuous_const.mul (continuous_inv_radial hr hR)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi1 hi2]
  rw [integral_cos, intervalIntegral.integral_const_mul, integral_inv_radial hr hR]
  rw [Real.sin_two_pi, Real.sin_zero]
  field_simp
  ring

/-- The Willmore energy `∫∫ H² dA` of the torus of revolution with radii `R > r > 0`. -/
