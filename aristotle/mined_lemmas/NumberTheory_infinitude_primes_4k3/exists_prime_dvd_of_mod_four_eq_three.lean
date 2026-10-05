/-
# Infinitude Primes 4 K 3
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.infinitude_primes_4k3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace NumberTheory

/-- Every natural number congruent to `3` modulo `4` has a prime divisor
congruent to `3` modulo `4`. -/

theorem exists_prime_dvd_of_mod_four_eq_three :
    ∀ n : ℕ, n % 4 = 3 → ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hn1 : n ≠ 1 := by omega
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hn1
    have hp2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨k, rfl⟩ := hpd
      omega
    have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases hp4 with h1 | h3
    · -- factor out `p` and recurse on `n / p`
      obtain ⟨m, rfl⟩ := hpd
      have hm : m % 4 = 3 := by
        have := Nat.mul_mod p m 4
        rw [h1] at this
        omega
      have hp1lt : 1 < p := hp.one_lt
      have hmpos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · simp at hn
        · exact h
      have hlt : m < p * m := by
        calc m = 1 * m := (one_mul m).symm
        _ < p * m := Nat.mul_lt_mul_of_lt_of_le hp1lt (le_refl m) hmpos
      obtain ⟨q, hq, hqd, hq4⟩ := ih m hlt hm
      exact ⟨q, hq, hqd.mul_left p, hq4⟩
    · exact ⟨p, hp, hpd, h3⟩

/-- **There are infinitely many primes congruent to `3` modulo `4`.**
For every `N` there is a prime `p` with `N < p` and `p % 4 = 3`. -/
