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

/-
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.MersennePerfect

open ArithmeticFunction Finset
open scoped sigma

/-- The set of even perfect numbers. -/

lemma exists_mersenne_of_even_perfect {n : ℕ} (ev : Even n) (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = euclidMap k := by
  obtain ⟨k, m, rfl, hm⟩ := exists_two_pow_mul_odd perf.2
  have hpos := perf.2
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h] at hpos
    · exact h
  have hm2 : ¬ (2 ∣ m) := by rwa [even_iff_two_dvd] at hm
  have hModd : Odd (mersenne (k + 1)) := odd_mersenne_succ k
  have hcop : Nat.Coprime (2 ^ k) m :=
    Nat.Coprime.pow_left _ ((Nat.prime_two.coprime_iff_not_dvd).2 hm2)
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_two_pow] at perf
  have hdvd : mersenne (k + 1) ∣ m := by
    have h1 : mersenne (k + 1) ∣ 2 ^ (k + 1) * m := ⟨σ 1 m, by rw [perf]; ring⟩
    exact Nat.Coprime.dvd_of_dvd_mul_left ((hModd.coprime_two_right).pow_right _) h1
  obtain ⟨j, rfl⟩ := hdvd
  have hMpos : 0 < mersenne (k + 1) := by
    rcases Nat.eq_zero_or_pos (mersenne (k + 1)) with h | h
    · simp [h] at hmpos
    · exact h
  have key : σ 1 (mersenne (k + 1) * j) = 2 ^ (k + 1) * j := by
    refine Nat.eq_of_mul_eq_mul_left hMpos ?_
    rw [perf]; ring
  have h2 : σ 1 (mersenne (k + 1) * j) = mersenne (k + 1) * j + j := by
    rw [key, ← succ_mersenne (k + 1)]; ring
  have h3 : ∑ i ∈ (mersenne (k + 1) * j).properDivisors, i = j := by
    rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self] at h2
    omega
  have hjdvd : (∑ i ∈ (mersenne (k + 1) * j).properDivisors, i) ∣ (mersenne (k + 1) * j) := by
    rw [h3]; exact Dvd.intro_left _ rfl
  rcases Nat.sum_properDivisors_dvd hjdvd with h | h
  · have hj1 : j = 1 := by omega
    subst hj1
    refine ⟨k, ?_, by simp [euclidMap]⟩
    rw [mul_one] at h
    exact (Nat.sum_properDivisors_eq_one_iff_prime).1 h
  · exfalso
    have hjm : j = mersenne (k + 1) * j := by omega
    have hM1 : mersenne (k + 1) = 1 := by
      have hjpos : 0 < j := by
        rcases Nat.eq_zero_or_pos j with h' | h'
        · simp [h'] at hmpos
        · exact h'
      nlinarith [hjm]
    have hk0 : k = 0 := by
      by_contra hk
      have hlt : mersenne 1 < mersenne (k + 1) := mersenne_lt_mersenne.2 (by omega)
      rw [hM1] at hlt
      simp [mersenne] at hlt
    subst hk0
    rw [hM1] at ev
    simp at ev
    exact hm (by simpa [hM1] using ev)

/-- The Euclid–Euler characterisation of even perfect numbers. -/
