/-!
# Test Pair Nonneg
Category: Riemann Program
Target: Riemann.WeilPositivity.test_pair_nonneg
Statement: For all real x, y : 0 <= 2*x^2 + 2*x*y + 2*y^2. This is the quadratic form of the 2x2 real symmetric matrix [[2,1],[1,2]] (a positive-semidefinite compression of Weil's Hermitian explicit-formula form on a test pair); equivalently (x+y)^2 + x^2 + y^2 >= 0.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
/-!
# Test Pair Nonneg
Category: Riemann Program
Target: Riemann.WeilPositivity.test_pair_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
-- (The header above is wrapped in a block comment because Lean 4 requires
-- `import` commands to precede any module docstring.)


namespace Riemann.WeilPositivity

/-- **Test pair nonnegativity.** The quadratic form of the positive-semidefinite
real symmetric matrix `[[2,1],[1,2]]` is nonnegative: for all real `x`, `y`,
`0 ≤ 2*x^2 + 2*x*y + 2*y^2`, since it equals `(x + y)^2 + x^2 + y^2`. -/
theorem test_pair_nonneg (x y : ℝ) : 0 ≤ 2 * x ^ 2 + 2 * x * y + 2 * y ^ 2 := by
  have h : 2 * x ^ 2 + 2 * x * y + 2 * y ^ 2 = (x + y) ^ 2 + x ^ 2 + y ^ 2 := by ring
  rw [h]
  positivity

end Riemann.WeilPositivity

