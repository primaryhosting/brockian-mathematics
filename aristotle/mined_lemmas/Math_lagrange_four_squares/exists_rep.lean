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

private theorem exists_rep {m : ℤ} (hm : 0 < m) (hodd : m % 2 = 1) (x : ℤ) :
    ∃ y t : ℤ, x = y + m * t ∧ 2 * |y| < m := by
  refine ⟨(x + m / 2) % m - m / 2, (x + m / 2) / m, ?_, ?_⟩
  · have := Int.emod_add_mul_ediv (x + m / 2) m
    omega
  · have h1 : 0 ≤ (x + m / 2) % m := Int.emod_nonneg _ (by omega)
    have h2 : (x + m / 2) % m < m := Int.emod_lt_of_pos _ hm
    rcases abs_cases ((x + m / 2) % m - m / 2) with ⟨he, _⟩ | ⟨he, _⟩ <;> omega

/-- If `2 * |A| < M` then `4 * A ^ 2 < M ^ 2`. -/
