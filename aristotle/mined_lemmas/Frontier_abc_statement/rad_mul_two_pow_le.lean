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

lemma rad_mul_two_pow_le {b j : ℕ} (hb : 0 < b) (h : 2 ^ (j + 1) ∣ b) :
    2 ^ j * rad b ≤ b := by
  set v := b.factorization 2 with hv
  have hvj : j + 1 ≤ v := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hb.ne').mp h
  set m := b / 2 ^ v with hm
  have hsplit : 2 ^ v * m = b := Nat.ordProj_mul_ordCompl_eq_self b 2
  have hmpos : 0 < m := Nat.ordCompl_pos 2 hb.ne'
  have hcop : Nat.Coprime (2 ^ v) m :=
    (Nat.coprime_ordCompl Nat.prime_two hb.ne').pow_left _
  have hradb : rad b = 2 * rad m := by
    rw [← hsplit, rad_mul_of_coprime (by positivity) hmpos.ne' hcop,
      rad_prime_pow Nat.prime_two (by omega)]
  have hmle : rad m ≤ m := rad_le_self hmpos
  calc 2 ^ j * rad b = 2 ^ (j + 1) * rad m := by rw [hradb]; ring
    _ ≤ 2 ^ v * m := Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hvj) hmle
    _ = b := hsplit

/-- `2 ^ (k + 3)` divides `3 ^ 2 ^ (k + 1) - 1`. -/
