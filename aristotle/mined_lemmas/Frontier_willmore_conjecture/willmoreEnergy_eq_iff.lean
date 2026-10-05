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

theorem willmoreEnergy_eq_iff {R r : ℝ} (hr : 0 < r) (hR : r < R) :
    willmoreEnergy R r = 2 * π ^ 2 ↔ R = Real.sqrt 2 * r := by
  have hR0 : 0 < R := lt_trans hr hR
  have hs := sqrt_sub_pos hr hR
  have hsqnn : (0:ℝ) ≤ R ^ 2 - r ^ 2 := by nlinarith
  have hs2 := Real.sq_sqrt hsqnn
  have hpi : (0:ℝ) < π ^ 2 := by positivity
  constructor
  · intro h
    rw [willmoreEnergy_eq hr hR, div_eq_iff (by positivity)] at h
    have key : R ^ 2 = 2 * (r * Real.sqrt (R ^ 2 - r ^ 2)) := by
      have := mul_left_cancel₀ (ne_of_gt hpi) (a := π ^ 2)
        (b := R ^ 2) (c := 2 * (r * Real.sqrt (R ^ 2 - r ^ 2)))
      apply this
      linarith [h]
    have hzero : (R ^ 2 - 2 * r ^ 2) ^ 2 = 0 := by nlinarith [key, hs2]
    have h2 : R ^ 2 = 2 * r ^ 2 := by nlinarith [pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero]
    have hc : (Real.sqrt 2 * r) ^ 2 = 2 * r ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith [Real.sqrt_nonneg 2, mul_pos (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)) hr]
  · intro h
    subst h
    exact willmoreEnergy_clifford hr

/-- **The Willmore conjecture for tori of revolution (Willmore's theorem).**

For the family of embedded genus-one surfaces given by the tori of revolution with radii
`R > r > 0`, the Willmore energy `W = ∫∫ H² dA` — computed here from the parametrization
via the first and second fundamental forms — is bounded below by `2π²`, this value is
attained by the Clifford torus `R = √2 r`, and the Clifford torus is the *only* torus of
revolution attaining it.

This is the classical base case of the Willmore conjecture, proved in full generality for
all genus-one immersed surfaces in `S³` (equivalently `ℝ³`) by Marques and Neves. -/
