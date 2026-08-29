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

namespace OddZumkeller

/-- A positive natural number `n` is a *Zumkeller number* if its set of divisors can be split
into two parts having the same sum. -/

theorem three_le_card_primeFactors {n : ℕ} (hodd : Odd n) (h : Zumkeller n) :
    3 ≤ n.primeFactors.card := by
  by_contra hcon
  push_neg at hcon
  have hcard : n.primeFactors.card ≤ 2 := by omega
  have hn : 0 < n := h.1
  have hsig : 2 * n ≤ ∑ d ∈ n.divisors, d := two_mul_le_sum_divisors_of_zumkeller h
  have hkey := sum_divisors_mul_prod_pred_le n
  have hstep : 2 * n * ∏ p ∈ n.primeFactors, (p - 1) ≤ n * ∏ p ∈ n.primeFactors, p :=
    le_trans (Nat.mul_le_mul_right _ hsig) hkey
  have hmain : 2 * ∏ p ∈ n.primeFactors, (p - 1) ≤ ∏ p ∈ n.primeFactors, p := by
    have : n * (2 * ∏ p ∈ n.primeFactors, (p - 1)) ≤ n * ∏ p ∈ n.primeFactors, p := by
      calc n * (2 * ∏ p ∈ n.primeFactors, (p - 1))
          = 2 * n * ∏ p ∈ n.primeFactors, (p - 1) := by ring
        _ ≤ n * ∏ p ∈ n.primeFactors, p := hstep
    exact Nat.le_of_mul_le_mul_left this hn
  interval_cases hc : n.primeFactors.card
  · -- no prime factors
    rw [Finset.card_eq_zero] at hc
    rw [hc] at hmain
    simp at hmain
  · -- one prime factor
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
    have hp3 : 3 ≤ p := three_le_of_mem_primeFactors_odd hodd (by rw [hp]; exact Finset.mem_singleton_self p)
    rw [hp] at hmain
    simp only [Finset.prod_singleton] at hmain
    omega
  · -- two prime factors
    obtain ⟨p, q, hpq, hset⟩ := Finset.card_eq_two.mp hc
    have hp3 : 3 ≤ p := three_le_of_mem_primeFactors_odd hodd (by rw [hset]; simp)
    have hq3 : 3 ≤ q := three_le_of_mem_primeFactors_odd hodd (by rw [hset]; simp)
    rw [hset] at hmain
    rw [Finset.prod_pair hpq, Finset.prod_pair hpq] at hmain
    -- both are odd primes, hence one of them is at least 5
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hset]; simp)
    have hqq : q.Prime := Nat.prime_of_mem_primeFactors (by rw [hset]; simp)
    have hp4 : p ≠ 4 := by rintro rfl; exact absurd hpp (by decide)
    have hq4 : q ≠ 4 := by rintro rfl; exact absurd hqq (by decide)
    have hp5 : 5 ≤ p ∨ 5 ≤ q := by omega
    obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = b + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hmain
    rcases hp5 with h5 | h5 <;> nlinarith [hmain]

/-- The divisors of `945`. -/
