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
theorem infinitude_primes_4k3 (N : ℕ) : ∃ p : ℕ, p.Prime ∧ N < p ∧ p % 4 = 3 := by
  set n : ℕ := 4 * Nat.factorial N - 1 with hn
  have hfac : 0 < Nat.factorial N := Nat.factorial_pos N
  have hn4 : n % 4 = 3 := by
    have : 4 * Nat.factorial N - 1 = 4 * (Nat.factorial N - 1) + 3 := by omega
    rw [hn, this]
    omega
  obtain ⟨p, hp, hpd, hp4⟩ := exists_prime_dvd_of_mod_four_eq_three n hn4
  refine ⟨p, hp, ?_, hp4⟩
  by_contra hle
  push_neg at hle
  have hdvd : p ∣ Nat.factorial N := Nat.dvd_factorial hp.pos hle
  have h1 : p ∣ 4 * Nat.factorial N := hdvd.mul_left 4
  have h2 : p ∣ 4 * Nat.factorial N - n := Nat.dvd_sub h1 hpd
  have h3 : 4 * Nat.factorial N - n = 1 := by omega
  rw [h3] at h2
  exact absurd (Nat.le_of_dvd one_pos h2) (by have := hp.two_le; omega)

/-- The set of primes congruent to `3` modulo `4` is infinite. -/
theorem setOf_primes_4k3_infinite : {p : ℕ | p.Prime ∧ p % 4 = 3}.Infinite := by
  apply Set.infinite_of_not_bddAbove
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

