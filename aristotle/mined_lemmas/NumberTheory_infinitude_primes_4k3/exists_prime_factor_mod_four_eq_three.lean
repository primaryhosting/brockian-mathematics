/-
# Infinitude Primes 4 K 3
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.infinitude_primes_4k3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace NumberTheory

/-! ### An elementary Euclid-style argument

Every natural number congruent to `3` mod `4` has a prime factor congruent to `3` mod `4`,
because a product of numbers congruent to `1` mod `4` is again congruent to `1` mod `4`.
Applying this to `4 * N ! - 1` produces a prime `> N` congruent to `3` mod `4`. -/

/-- If `q ≡ 1 [MOD 4]` and `q * m ≡ 3 [MOD 4]`, then `m ≡ 3 [MOD 4]`. -/

theorem exists_prime_factor_mod_four_eq_three :
    ∀ n : ℕ, n % 4 = 3 → ∃ p, Nat.Prime p ∧ p ∣ n ∧ p % 4 = 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hn1 : n ≠ 1 := by omega
    obtain ⟨q, hq, m, hm⟩ : ∃ q, Nat.Prime q ∧ ∃ m, n = q * m :=
      ⟨n.minFac, Nat.minFac_prime hn1, (Nat.minFac_dvd n).choose,
        (Nat.minFac_dvd n).choose_spec⟩
    -- `n` is odd, hence so is any prime factor of it
    have hqdvd : q ∣ n := ⟨m, hm⟩
    have hodd : q % 2 = 1 := by
      rcases hq.eq_two_or_odd with h2 | h1
      · subst h2; omega
      · exact h1
    have hq1 : 1 < q := hq.one_lt
    rcases (by omega : q % 4 = 1 ∨ q % 4 = 3) with h1 | h3
    · -- the prime factor is `1` mod `4`: pass to the strictly smaller cofactor
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · rw [Nat.mul_zero] at hm; omega
        · exact h
      have hmmod : m % 4 = 3 := mod_four_of_mul_left_one h1 (by rw [← hm]; exact hn)
      have hmlt : m < n := by rw [hm]; nlinarith
      obtain ⟨p, hp', hpd, hpm⟩ := ih m hmlt hmmod
      exact ⟨p, hp', hpd.trans ⟨q, by rw [hm, Nat.mul_comm]⟩, hpm⟩
    · exact ⟨q, hq, hqdvd, h3⟩

/-- **Infinitude of primes congruent to `3` mod `4`.**

For every `N` there is a prime `p` with `N < p` and `p % 4 = 3`.

Elementary Euclid-style proof: a prime factor `p ≡ 3 [MOD 4]` of `4 * N ! - 1` cannot be `≤ N`,
since such a prime divides `N !` and hence would divide `1`. -/
