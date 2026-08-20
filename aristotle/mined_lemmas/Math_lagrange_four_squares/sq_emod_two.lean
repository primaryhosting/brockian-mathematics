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

private theorem sq_emod_two (x : ℤ) : x ^ 2 % 2 = x % 2 := by
  have h : Even (x ^ 2) ↔ Even x := by simp [Int.even_pow]
  rcases Int.even_or_odd x with hx | hx
  · rw [Int.even_iff.mp (h.mpr hx), Int.even_iff.mp hx]
  · have h1 : ¬ Even x := Int.not_even_iff_odd.mpr hx
    have h2 : ¬ Even (x ^ 2) := fun hc => h1 (h.mp hc)
    rw [Int.not_even_iff.mp h2, Int.not_even_iff.mp h1]

/-- Halving step: if `a ≡ b` and `c ≡ d` mod `2`, a representation of `2 * m` gives one of `m`. -/
