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

lemma sq_mod_four (n : ℕ) : n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1 := by
  have h : n ^ 2 % 4 = (n % 4) ^ 2 % 4 := by
    rw [Nat.pow_mod]
  have h4 : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases hn : (n % 4) <;> simp [h]

/-- **Fermat's two–squares theorem.** A prime `p` is a sum of two squares if and only if
`p = 2` or `p ≡ 1 (mod 4)`. -/
