/-!
# Sum Two Squares
Category: Pure Mathematics
Target: Math.sum_two_squares
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- A square is congruent to `0` or `1` modulo `4`. -/

lemma sum_sq_mod_four_ne_three (a b : ℕ) : (a ^ 2 + b ^ 2) % 4 ≠ 3 := by
  have ha := sq_mod_four a
  have hb := sq_mod_four b
  omega

/-- **Fermat's two-square theorem** (prime case): a prime `p` is a sum of two squares
iff `p = 2` or `p ≡ 1 (mod 4)`. -/
