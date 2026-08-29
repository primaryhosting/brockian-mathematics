/-
# Infinitude Primes 4 K 3
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.infinitude_primes_4k3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace NumberTheory

/-- Any natural number congruent to `3` modulo `4` has a prime divisor congruent to `3`
modulo `4`.  (A product of numbers that are `1` mod `4` is again `1` mod `4`.) -/
theorem exists_prime_factor_mod_four_eq_three :
    ∀ n : ℕ, n % 4 = 3 → ∃ p, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hn1 : n ≠ 1 := by omega
    set p := n.minFac with hp
    have hpp : p.Prime := Nat.minFac_prime hn1
    have hpd : p ∣ n := Nat.minFac_dvd n
    -- `n` is odd, hence so is its least prime factor `p`
    have hodd : p % 2 = 1 := by
      rcases hpp.eq_two_or_odd with h2 | h2
      · exfalso
        have h2n : (2 : ℕ) ∣ n := h2 ▸ hpd
        omega
      · exact h2
    have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases hp4 with h1 | h3
    · -- divide out the factor `p ≡ 1 [MOD 4]` and recurse on the cofactor
      obtain ⟨m, hm⟩ := hpd
      have hp2 : 2 ≤ p := hpp.two_le
      have hmpos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h, Nat.mul_zero] at hm; omega
        · exact h
      have hmlt : m < n := by
        calc m < 2 * m := by omega
          _ ≤ p * m := Nat.mul_le_mul_right m hp2
          _ = n := hm.symm
      have hm4 : m % 4 = 3 := by
        have key : n % 4 = m % 4 := by
          simp [hm, Nat.mul_mod, h1]
        omega
      obtain ⟨q, hq, hqd, hq4⟩ := ih m hmlt hm4
      exact ⟨q, hq, hqd.trans ⟨p, by rw [hm, Nat.mul_comm]⟩, hq4⟩
    · exact ⟨p, hpp, hpd, h3⟩

/-- **There are infinitely many primes congruent to `3` modulo `4`**: for every `N` there
exists a prime `p` with `N < p` and `p % 4 = 3`. -/
theorem infinitude_primes_4k3 (N : ℕ) : ∃ p, Nat.Prime p ∧ N < p ∧ p % 4 = 3 := by
  have hfac : 1 ≤ Nat.factorial N := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero N)
  set n := 4 * Nat.factorial N - 1 with hn
  have hn4 : n % 4 = 3 := by omega
  obtain ⟨p, hpp, hpd, hp4⟩ := exists_prime_factor_mod_four_eq_three n hn4
  refine ⟨p, hpp, ?_, hp4⟩
  by_contra hle
  push_neg at hle
  have hdvd : p ∣ Nat.factorial N := Nat.dvd_factorial hpp.pos hle
  have h4 : p ∣ 4 * Nat.factorial N := hdvd.mul_left 4
  have hone : p ∣ 1 := by
    have h := Nat.dvd_sub h4 hpd
    rwa [show 4 * Nat.factorial N - n = 1 by omega] at h
  exact absurd (Nat.le_of_dvd one_pos hone) (by have := hpp.two_le; omega)

/-- Restatement: the set of primes congruent to `3` modulo `4` is infinite. -/
theorem infinite_setOf_primes_4k3 : {p : ℕ | p.Prime ∧ p % 4 = 3}.Infinite := by
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨N, hN⟩
  obtain ⟨p, hpp, hpN, hp4⟩ := infinitude_primes_4k3 N
  exact absurd (hN (show p ∈ {p : ℕ | p.Prime ∧ p % 4 = 3} from ⟨hpp, hp4⟩)) (by omega)

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

