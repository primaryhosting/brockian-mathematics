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
theorem exists_prime_dvd_mod_four_eq_three :
    ∀ n : ℕ, n % 4 = 3 → ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hn1 : n ≠ 1 := by omega
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hn1
    obtain ⟨m, rfl⟩ := hqd
    have hq2 : q % 2 = 1 := by
      rcases hq.eq_two_or_odd with h | h
      · subst h; omega
      · exact h
    rcases (show q % 4 = 1 ∨ q % 4 = 3 by omega) with h4 | h4
    · -- `q ≡ 1 [MOD 4]`, so the cofactor `m` is again `≡ 3 [MOD 4]`, and is smaller.
      have hmod : (q * m) % 4 = m % 4 := by
        conv_lhs => rw [Nat.mul_mod, h4, one_mul, Nat.mod_mod_of_dvd _ (by norm_num)]
      have hm4 : m % 4 = 3 := by omega
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · subst h; simp at hn
        · exact h
      have hlt : m < q * m := by
        have := hq.two_le
        nlinarith
      obtain ⟨p, hp, hpd, hp4⟩ := ih m hlt hm4
      exact ⟨p, hp, hpd.mul_left q, hp4⟩
    · exact ⟨q, hq, Dvd.intro m rfl, h4⟩

/-- **There are infinitely many primes congruent to 3 modulo 4**: for every `N`
there exists a prime `p` with `N < p` and `p % 4 = 3`. -/
theorem infinitude_primes_4k3 (N : ℕ) : ∃ p : ℕ, p.Prime ∧ N < p ∧ p % 4 = 3 := by
  have hfac : 0 < Nat.factorial N := Nat.factorial_pos N
  set M : ℕ := 4 * Nat.factorial N - 1 with hM
  have hM4 : M % 4 = 3 := by omega
  obtain ⟨p, hp, hpd, hp4⟩ := exists_prime_dvd_mod_four_eq_three M hM4
  refine ⟨p, hp, ?_, hp4⟩
  by_contra hle
  push_neg at hle
  have h1 : p ∣ 4 * Nat.factorial N := (Nat.dvd_factorial hp.pos hle).mul_left 4
  have h2 : p ∣ 1 := by
    have hsub : 4 * Nat.factorial N - M = 1 := by omega
    simpa [hsub] using Nat.dvd_sub h1 hpd
  exact hp.one_lt.ne' (Nat.dvd_one.mp h2)

/-- The set of primes congruent to `3` modulo `4` is infinite. -/
theorem infinite_setOf_prime_mod_four_eq_three :
    {p : ℕ | p.Prime ∧ p % 4 = 3}.Infinite := by
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨N, hN⟩
  obtain ⟨p, hp, hlt, hp4⟩ := infinitude_primes_4k3 N
  exact absurd (hN ⟨hp, hp4⟩) (by omega)

end NumberTheory

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

