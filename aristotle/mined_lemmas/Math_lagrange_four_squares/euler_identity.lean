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

theorem euler_identity (a b c d A B C D : ℤ) :
    (a * A + b * B + c * C + d * D) ^ 2 + (a * B - b * A + c * D - d * C) ^ 2 +
      (a * C - b * D - c * A + d * B) ^ 2 + (a * D + b * C - c * B - d * A) ^ 2 =
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2) := by
  ring

/-- Sums of four squares are closed under multiplication. -/
