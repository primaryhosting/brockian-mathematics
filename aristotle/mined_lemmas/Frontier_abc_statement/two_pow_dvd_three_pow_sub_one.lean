/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
Mathlib does not state the `abc` conjecture. The closest existing material is
`UniqueFactorizationMonoid.radical` (`Mathlib/RingTheory/Radical.lean`), a general radical
of an element of a UFM, and the Mason–Stothers theorem
(`Mathlib/NumberTheory/FLT/MasonStothers.lean`), the polynomial analogue of `abc`.
Neither closes the statement below, so the radical for `ℕ` and both formulations of the
conjecture are set up here from scratch.
-/

namespace Frontier

open scoped BigOperators

/-- The radical of a natural number: the product of its distinct prime factors.
By convention `rad 0 = rad 1 = 1`. -/

lemma two_pow_dvd_three_pow_sub_one (k : ℕ) : 2 ^ (k + 3) ∣ 3 ^ 2 ^ (k + 1) - 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hx : 1 ≤ 3 ^ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
      obtain ⟨y, hy⟩ : ∃ y, 3 ^ 2 ^ (k + 1) = y + 1 := ⟨3 ^ 2 ^ (k + 1) - 1, by omega⟩
      have hsq : 3 ^ 2 ^ (k + 2) = (3 ^ 2 ^ (k + 1)) ^ 2 := by
        rw [← pow_mul, ← pow_succ]
      have hfac : 3 ^ 2 ^ (k + 2) - 1 = (3 ^ 2 ^ (k + 1) - 1) * (3 ^ 2 ^ (k + 1) + 1) := by
        rw [hsq, hy]
        have : (y + 1) ^ 2 = y * y + 2 * y + 1 := by ring
        rw [this]
        have : (y + 1 - 1) * (y + 1 + 1) = y * y + 2 * y := by
          simp only [Nat.add_sub_cancel]
          ring
        omega
      have heven : 2 ∣ 3 ^ 2 ^ (k + 1) + 1 := by
        have hodd : 3 ^ 2 ^ (k + 1) % 2 = 1 := Nat.pow_mod 3 _ 2 ▸ by simp
        omega
      rw [hfac]
      have : 2 ^ (k + 3) * 2 ∣ (3 ^ 2 ^ (k + 1) - 1) * (3 ^ 2 ^ (k + 1) + 1) :=
        mul_dvd_mul ih heven
      simpa [pow_succ] using this

/-- Each triple `1 + (3 ^ 2 ^ (k+1) - 1) = 3 ^ 2 ^ (k+1)` is an exceptional triple for
`ε = 0`. -/
