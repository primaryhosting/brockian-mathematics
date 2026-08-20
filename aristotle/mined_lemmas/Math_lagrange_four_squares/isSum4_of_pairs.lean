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

private theorem isSum4_of_pairs {a b c d m : ℤ} (hab : (a - b) % 2 = 0) (hcd : (c - d) % 2 = 0)
    (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 2 * m) : IsSum4 m := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, a - b = 2 * k := ⟨(a - b) / 2, by omega⟩
  obtain ⟨l, hl⟩ : ∃ l : ℤ, a + b = 2 * l := ⟨(a + b) / 2, by omega⟩
  obtain ⟨i, hi⟩ : ∃ i : ℤ, c - d = 2 * i := ⟨(c - d) / 2, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j : ℤ, c + d = 2 * j := ⟨(c + d) / 2, by omega⟩
  refine ⟨k, l, i, j, ?_⟩
  have h4 : 4 * (k ^ 2 + l ^ 2 + i ^ 2 + j ^ 2) = 4 * m := by
    have e : (2 * k) ^ 2 + (2 * l) ^ 2 + (2 * i) ^ 2 + (2 * j) ^ 2 =
        2 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
      rw [← hk, ← hl, ← hi, ← hj]; ring
    rw [h] at e
    nlinarith [e]
  linarith

/-- If `2 * m` is a sum of four squares, so is `m`. -/
