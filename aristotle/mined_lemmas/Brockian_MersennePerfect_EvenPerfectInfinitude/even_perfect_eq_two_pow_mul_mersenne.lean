import Brockian.MersennePerfect

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

(Note: written as a plain block comment rather than a module docstring, since Lean 4
requires `import` commands to precede any module docstring.)
-/

import Mathlib

namespace Brockian.MersennePerfect

open Finset

/-- The set of exponents `p` for which the Mersenne number `2 ^ p - 1` is prime. -/

theorem even_perfect_eq_two_pow_mul_mersenne {n : ℕ} (hn : Even n) (hp : n.Perfect) :
    ∃ k, (mersenne (k + 1)).Prime ∧ n = 2 ^ k * mersenne (k + 1) := by
  have hn0 : 0 < n := hp.2
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn0.ne'
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h] at hn0
    · exact h
  have hk : 1 ≤ k := by
    by_contra hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [pow_zero, one_mul] at hn
    exact (Nat.not_even_iff_odd.mpr hm) hn
  set q := mersenne (k + 1) with hqdef
  have hqval : q = 2 ^ (k + 1) - 1 := rfl
  have hpow : 4 ≤ 2 ^ (k + 1) := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq3 : 3 ≤ q := by rw [hqval]; omega
  have hq1 : q + 1 = 2 ^ (k + 1) := by rw [hqval]; omega
  set S := ∑ i ∈ m.divisors, i with hS
  have hkey : q * S = 2 ^ (k + 1) * m := by
    have h2 := (Nat.perfect_iff_sum_divisors_eq_two_mul hn0).1 hp
    rw [sum_divisors_two_pow_mul_odd k hm] at h2
    rw [hqval, hS]
    rw [h2]
    ring
  have hqodd : Odd q := mersenne_succ_odd k
  have hcop : Nat.Coprime q (2 ^ (k + 1)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hqodd)
  have hqdvd : q ∣ m := by
    refine hcop.dvd_of_dvd_mul_left ?_
    exact ⟨S, hkey.symm⟩
  obtain ⟨j, hj⟩ := hqdvd
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · simp [h] at hj; omega
    · exact h
  have hSval : S = m + j := by
    have hq0 : 0 < q := by omega
    have : q * S = q * (m + j) := by
      rw [hkey, hj]
      calc 2 ^ (k + 1) * (q * j) = (q + 1) * (q * j) := by rw [hq1]
        _ = q * (q * j + j) := by ring
    exact Nat.eq_of_mul_eq_mul_left hq0 this
  have hprop : ∑ i ∈ m.properDivisors, i = j := by
    have := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := m)
    rw [← hS, hSval] at this
    omega
  have hjm : j < m := by
    rw [hj]
    nlinarith
  have hjdvd : j ∣ m := ⟨q, by rw [hj]; ring⟩
  have hm1 : 1 < m := by rw [hj]; nlinarith
  have hjone : j = 1 := by
    by_contra hne
    have h1mem : (1 : ℕ) ∈ m.properDivisors := Nat.one_mem_properDivisors_iff_one_lt.mpr hm1
    have hjmem : j ∈ m.properDivisors := Nat.mem_properDivisors.mpr ⟨hjdvd, hjm⟩
    have hsub : ({1, j} : Finset ℕ) ⊆ m.properDivisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h1mem
      · exact hjmem
    have hle : ∑ i ∈ ({1, j} : Finset ℕ), i ≤ ∑ i ∈ m.properDivisors, i :=
      Finset.sum_le_sum_of_subset hsub
    rw [Finset.sum_pair (Ne.symm hne), hprop] at hle
    omega
  subst hjone
  refine ⟨k, ?_, ?_⟩
  · have hmq : m = q := by omega
    rw [← hqdef, ← hmq]
    exact Nat.sum_properDivisors_eq_one_iff_prime.mp (by rw [hprop])
  · congr 1
    omega

/-- If there are infinitely many even perfect numbers, there are infinitely many
Mersenne primes. -/
