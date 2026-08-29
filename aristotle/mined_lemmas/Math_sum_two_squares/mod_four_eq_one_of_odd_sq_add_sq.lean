/-
# Sum Two Squares
Category: Pure Mathematics
Target: Math.sum_two_squares
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- A square is congruent to `0` or `1` modulo `4`. -/

lemma mod_four_eq_one_of_odd_sq_add_sq {n a b : ℕ} (hodd : n % 2 = 1)
    (h : a ^ 2 + b ^ 2 = n) : n % 4 = 1 := by
  rcases sq_mod_four a with ha | ha <;> rcases sq_mod_four b with hb | hb <;> omega

/-- **Fermat's two–squares theorem.** A prime `p` is a sum of two squares if and only if
`p = 2` or `p ≡ 1 (mod 4)`. -/
