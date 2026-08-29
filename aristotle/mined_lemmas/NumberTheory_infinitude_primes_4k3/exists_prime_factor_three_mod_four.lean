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

/-- Any natural number congruent to `3` mod `4` has a prime factor congruent to `3` mod `4`. -/

theorem exists_prime_factor_three_mod_four :
    ∀ m : ℕ, m % 4 = 3 → ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ p % 4 = 3 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    have hm1 : m ≠ 1 := by omega
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hm1
    -- `p` is odd, since `m` is odd
    have hmodd : m % 2 = 1 := by omega
    have hpodd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h2 | h2
      · exfalso
        subst h2
        obtain ⟨c, rfl⟩ := hpd
        omega
      · exact h2
    have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases hp4 with hp4 | hp4
    · -- `p ≡ 1 [MOD 4]`: pass to the cofactor
      obtain ⟨q, rfl⟩ := hpd
      have hq4 : q % 4 = 3 := by
        have := Nat.mul_mod p q 4
        rw [hp4] at this
        omega
      have hqlt : q < p * q := by
        have hq0 : 0 < q := by omega
        have hp2 : 2 ≤ p := hp.two_le
        calc q = 1 * q := (one_mul q).symm
        _ < p * q := by exact Nat.mul_lt_mul_of_lt_of_le hp2 (le_refl q) hq0
      obtain ⟨r, hr, hrd, hr4⟩ := ih q hqlt hq4
      exact ⟨r, hr, hrd.mul_left p, hr4⟩
    · exact ⟨p, hp, hpd, hp4⟩

/-- **Infinitude of primes congruent to 3 mod 4**: for every `N` there is a prime `p > N`
with `p % 4 = 3`. -/
