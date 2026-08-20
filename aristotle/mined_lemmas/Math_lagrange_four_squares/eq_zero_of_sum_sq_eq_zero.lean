/-
# Lagrange Four Squares
Category: Pure Mathematics
Target: Math.lagrange_four_squares
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: Lean 4 requires `import` commands to precede any module docstring (`/-! ... -/`),
-- so the header above is written as an ordinary block comment.

import Mathlib

/-!
This file contains a self-contained proof of Lagrange's four-square theorem, following
Lagrange's classical descent argument:

* `Math.euler_identity` : Euler's four-square identity;
* `Math.IsSum4.mul` : the sums of four squares are closed under multiplication;
* `Math.exists_mul_isSum4_of_prime` : some multiple `m * p` with `0 < m < p` of a prime `p`
  is a sum of four squares;
* `Math.isSum4_of_two_mul` and `Math.descent_odd` : the two descent steps;
* `Math.prime_isSum4` : every prime is a sum of four squares;
* `Math.lagrange_four_squares` : every natural number is a sum of four squares.
-/

namespace Math

/-- `IsSum4 n` states that the integer `n` is a sum of four integer squares. -/

private theorem eq_zero_of_sum_sq_eq_zero {A B C D : ℤ}
    (h : A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2 = 0) : A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 := by
  have hA : A ^ 2 = 0 := by nlinarith [sq_nonneg A, sq_nonneg B, sq_nonneg C, sq_nonneg D]
  have hB : B ^ 2 = 0 := by nlinarith [sq_nonneg A, sq_nonneg B, sq_nonneg C, sq_nonneg D]
  have hC : C ^ 2 = 0 := by nlinarith [sq_nonneg A, sq_nonneg B, sq_nonneg C, sq_nonneg D]
  have hD : D ^ 2 = 0 := by nlinarith [sq_nonneg A, sq_nonneg B, sq_nonneg C, sq_nonneg D]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all [pow_eq_zero_iff]

/-- The parity of `x ^ 2` is the parity of `x`. -/
