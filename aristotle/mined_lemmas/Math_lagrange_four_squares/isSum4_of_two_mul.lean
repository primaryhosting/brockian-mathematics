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

theorem isSum4_of_two_mul {m : ℤ} (h : IsSum4 (2 * m)) : IsSum4 m := by
  obtain ⟨a, b, c, d, h⟩ := h
  have ha := sq_emod_two a
  have hb := sq_emod_two b
  have hc := sq_emod_two c
  have hd := sq_emod_two d
  have hsum : (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) % 2 = 0 := by omega
  by_cases h1 : (a - b) % 2 = 0
  · exact isSum4_of_pairs h1 (show (c - d) % 2 = 0 by omega) h
  · by_cases h2 : (a - c) % 2 = 0
    · exact isSum4_of_pairs (a := a) (b := c) (c := b) (d := d) h2
        (show (b - d) % 2 = 0 by omega) (by linarith)
    · exact isSum4_of_pairs (a := a) (b := d) (c := b) (d := c)
        (show (a - d) % 2 = 0 by omega) (show (b - c) % 2 = 0 by omega) (by linarith)

/-- Representatives of least absolute value modulo an odd number `m`. -/
