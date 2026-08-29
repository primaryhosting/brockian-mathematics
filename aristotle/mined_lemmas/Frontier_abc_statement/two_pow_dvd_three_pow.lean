import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Frontier

/-- The radical of a natural number: the product of its distinct prime factors. -/

lemma two_pow_dvd_three_pow (n : ℕ) : 2 ^ (n + 3) ∣ 3 ^ (2 ^ (n + 1)) - 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      obtain ⟨v, hv⟩ := ih
      have hA : (3 : ℕ) ^ (2 ^ (n + 2)) = (3 ^ (2 ^ (n + 1))) ^ 2 := by
        rw [← pow_mul]
        ring_nf
      have hone : 1 ≤ (3 : ℕ) ^ (2 ^ (n + 1)) := Nat.one_le_pow _ _ (by norm_num)
      obtain ⟨t, ht⟩ : ∃ t, (3 : ℕ) ^ (2 ^ (n + 1)) = t + 1 :=
        ⟨3 ^ (2 ^ (n + 1)) - 1, by omega⟩
      have htv : t = 2 ^ (n + 3) * v := by omega
      refine ⟨v * (2 ^ (n + 2) * v + 1), ?_⟩
      have hexp : (t + 1) ^ 2 = t ^ 2 + 2 * t + 1 := by ring
      rw [hA, ht, hexp]
      have : t ^ 2 + 2 * t + 1 - 1 = t ^ 2 + 2 * t := by omega
      rw [this, htv]
      ring

/-! ### The base case `ε = 0`: infinitely many exceptions -/

/-- The witnesses `(1, 3 ^ (2 ^ (n+1)) - 1, 3 ^ (2 ^ (n+1)))`. -/
