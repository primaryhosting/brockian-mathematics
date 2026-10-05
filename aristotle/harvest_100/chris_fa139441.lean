/-!
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxRecDepth 100000

namespace Brockian

/-- Candidate divisors `2, 3, …, 47`: enough to certify primality below `48^2 = 2304`. -/
def trialDivisors : List ℕ := List.range' 2 46

/-- A kernel-friendly trial-division primality test, correct for inputs below `2304`. -/
def isPrimeB (n : ℕ) : Bool :=
  decide (2 ≤ n) && trialDivisors.all (fun d => decide (n < d * d) || decide (n % d ≠ 0))

theorem prime_of_isPrimeB {n : ℕ} (hn : n < 2304) (h : isPrimeB n = true) : Nat.Prime n := by
  rw [isPrimeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨h2, hall⟩ := h
  by_contra hp
  have hne : n ≠ 1 := by omega
  have hmp : Nat.Prime n.minFac := Nat.minFac_prime hne
  have hsq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hp
  have hlt : n.minFac < 48 := by nlinarith [hmp.two_le, sq_nonneg n.minFac]
  have hmem : n.minFac ∈ trialDivisors := by
    rw [trialDivisors, List.mem_range'_1]
    exact ⟨hmp.two_le, by omega⟩
  have hthis := hall _ hmem
  rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hthis
  have hdvd : n % n.minFac = 0 := Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd n)
  rcases hthis with h1 | h1
  · nlinarith [hsq]
  · exact h1 hdvd

/-- The wheel of admissible small summands: all primes up to `73`. -/
def wheel : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73]

/-- `goodB N` checks that `N` is the sum of a wheel prime and another prime. -/
def goodB (N : ℕ) : Bool :=
  wheel.any (fun p => decide (p ≤ N) && isPrimeB p && isPrimeB (N - p))

theorem wheel_check : ((List.range' 2 1152).all (fun n => goodB (2 * n))) = true := by decide

/-- **Goldbach with wheel modulus 1153, K = 2.**
For every `n` with `2 ≤ n ≤ 1153`, the even number `2 * n` is a sum of two primes,
where the smaller summand can be chosen from the wheel of primes up to `73`. -/
theorem GoldbachWheelK2_1153 (n : ℕ) (h2 : 2 ≤ n) (h1153 : n ≤ 1153) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≤ 73 ∧ p + q = 2 * n := by
  have hmem : n ∈ List.range' 2 1152 := by
    rw [List.mem_range'_1]; omega
  have hg : goodB (2 * n) = true := by
    have := wheel_check
    rw [List.all_eq_true] at this
    exact this _ hmem
  rw [goodB, List.any_eq_true] at hg
  obtain ⟨p, hpw, hp⟩ := hg
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨hple, hpp⟩, hqp⟩ := hp
  have hp73 : p ≤ 73 := by
    rw [wheel] at hpw
    fin_cases hpw <;> norm_num
  refine ⟨p, 2 * n - p, prime_of_isPrimeB (by omega) hpp, prime_of_isPrimeB (by omega) hqp,
    hp73, by omega⟩

end Brockian

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

