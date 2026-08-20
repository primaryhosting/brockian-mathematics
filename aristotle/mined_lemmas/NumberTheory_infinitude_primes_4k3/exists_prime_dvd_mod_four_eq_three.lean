/-
# Infinitude Primes 4 K 3
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.infinitude_primes_4k3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Infinitude Primes 4 K 3
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.infinitude_primes_4k3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace NumberTheory

/-- Every natural number congruent to `3` modulo `4` has a prime divisor
that is itself congruent to `3` modulo `4`. -/

theorem exists_prime_dvd_mod_four_eq_three :
    ∀ n : ℕ, n % 4 = 3 → ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hn1 : n ≠ 1 := by omega
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hn1
    by_cases hp4 : p % 4 = 3
    · exact ⟨p, hp, hpd, hp4⟩
    · -- `p` is odd, hence `p % 4 = 1`; peel it off and recurse.
      obtain ⟨m, rfl⟩ := hpd
      have hp2 : p ≠ 2 := by rintro rfl; omega
      have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
      have hp41 : p % 4 = 1 := by omega
      have hmod : (p * m) % 4 = m % 4 := by
        conv_lhs => rw [Nat.mul_mod, hp41]
        simp [Nat.mod_mod_of_dvd]
      have hm : m % 4 = 3 := by omega
      have hmlt : m < p * m := by
        have hm0 : 0 < m := by omega
        have := hp.two_le
        calc m = 1 * m := (one_mul m).symm
          _ < p * m := by exact Nat.mul_lt_mul_of_lt_of_le (by omega) le_rfl hm0
      obtain ⟨q, hq, hqd, hq4⟩ := ih m hmlt hm
      exact ⟨q, hq, hqd.mul_left p, hq4⟩

/-- **Infinitude of primes congruent to 3 mod 4.**
For every `N` there is a prime `p` with `N < p` and `p % 4 = 3`. -/
