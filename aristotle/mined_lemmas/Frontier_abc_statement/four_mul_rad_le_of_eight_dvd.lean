/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open scoped Real

/-- The radical of a natural number: the product of its distinct prime divisors. -/

lemma four_mul_rad_le_of_eight_dvd {m : ℕ} (hm : 0 < m) (h8 : 8 ∣ m) : 4 * rad m ≤ m := by
  obtain ⟨e, t, ht, hmt⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' 2 (by norm_num)
  have htpos : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h; simp at hmt; omega
    · exact h
  have h2t : Nat.Coprime 2 t := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr ht
  have hcop : Nat.Coprime (2 ^ e) t := Nat.Coprime.pow_left _ h2t
  have he : 3 ≤ e := by
    have h1 : (2 : ℕ) ^ 3 ∣ 2 ^ e * t := by rw [← hmt]; simpa using h8
    have h2 : (2 : ℕ) ^ 3 ∣ 2 ^ e :=
      Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left 3 h2t) h1
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2
  have hrad : rad m = 2 * rad t := by
    rw [hmt, rad_mul_of_coprime hcop (by positivity) htpos.ne', rad_pow 2 (by omega),
      rad_prime (by norm_num)]
  have hrt : rad t ≤ t := rad_le t htpos
  have h8e : (8 : ℕ) ≤ 2 ^ e := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  calc 4 * rad m = 8 * rad t := by rw [hrad]; ring
    _ ≤ 8 * t := Nat.mul_le_mul_left _ hrt
    _ ≤ 2 ^ e * t := Nat.mul_le_mul_right _ h8e
    _ = m := hmt.symm

/-- An abc-triple: positive coprime `a`, `b` with `a + b = c`. -/
structure ABCTriple (a b c : ℕ) : Prop where
  ha : 0 < a
  hb : 0 < b
  hsum : a + b = c
  hcop : Nat.Coprime a b

/-- The set of abc-triples that are exceptional for the exponent `1 + ε`, i.e. those
with `c > rad (a * b * c) ^ (1 + ε)`. -/
