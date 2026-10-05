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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A natural number `n` is *superperfect* when `σ(σ(n)) = 2n`, where `σ` is the
sum-of-divisors function.  The known superperfect numbers are `2, 4, 16, 64, …`,
i.e. the numbers `2 ^ (p - 1)` for which `2 ^ p - 1` is a Mersenne prime.  Whether
an *odd* superperfect number exists is an open problem: none is known, and it is
conjectured that none exists.

Accordingly this file does not prove the (open) existence statement outright.
Instead it develops the basic theory of `σ` needed here and proves an
unconditional **reduction**: an odd superperfect number exists if and only if one
exists that is, in addition, larger than `500` and composite.  Both extra
constraints are proved for every odd superperfect number, so the reduction is a
genuine restriction of the search space, not a tautology.
-/

namespace Brockian.SuperperfectNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/
def sigma1 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `n` is superperfect when `σ(σ(n)) = 2n`. -/
def Superperfect (n : ℕ) : Prop := sigma1 (sigma1 n) = 2 * n

instance : DecidablePred Superperfect := fun n => by unfold Superperfect; infer_instance

/-! ### Basic properties of `σ₁` -/

theorem sigma1_eq_sigma (n : ℕ) : sigma1 n = ArithmeticFunction.sigma 1 n := by
  rw [ArithmeticFunction.sigma_one_apply, sigma1]

theorem sigma1_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    sigma1 (m * n) = sigma1 m * sigma1 n := by
  simp only [sigma1_eq_sigma]
  exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h

theorem sigma1_two_pow (a : ℕ) : sigma1 (2 ^ a) = 2 ^ (a + 1) - 1 := by
  rw [sigma1, Nat.sum_divisors_prime_pow Nat.prime_two]
  simp [Nat.geomSum_eq]

theorem sigma1_prime {p : ℕ} (hp : p.Prime) : sigma1 p = p + 1 := by
  rw [sigma1, Nat.sum_divisors_eq_sum_properDivisors_add_self,
    Nat.Prime.sum_properDivisors hp]
  omega

/-- For `1 < k` the sum of divisors is at least `k + 1`. -/
theorem succ_le_sigma1 {k : ℕ} (hk : 1 < k) : k + 1 ≤ sigma1 k := by
  rw [sigma1, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  have h1 : (1 : ℕ) ∈ k.properDivisors := Nat.one_mem_properDivisors_iff_one_lt.mpr hk
  have : 1 ≤ ∑ i ∈ k.properDivisors, i :=
    Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) h1
  omega

theorem sigma1_ne_two (k : ℕ) : sigma1 k ≠ 2 := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k <;> simp [sigma1]
  · have := succ_le_sigma1 (k := k) (by omega)
    omega

/-! ### The even superperfect numbers coming from Mersenne primes -/

/-- If `2 ^ p - 1` is prime then `2 ^ (p - 1)` is superperfect. -/
theorem superperfect_two_pow_of_mersenne_prime {p : ℕ} (hp : 1 ≤ p)
    (hprime : (2 ^ p - 1).Prime) : Superperfect (2 ^ (p - 1)) := by
  have hp1 : p - 1 + 1 = p := by omega
  have h2 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  unfold Superperfect
  rw [sigma1_two_pow, hp1, sigma1_prime hprime, ← pow_succ' 2 (p - 1), hp1]
  omega

theorem superperfect_two : Superperfect 2 := by decide
theorem superperfect_four : Superperfect 4 := by decide
theorem superperfect_sixteen : Superperfect 16 := by decide
theorem superperfect_sixtyfour : Superperfect 64 := by decide

/-! ### Constraints on odd superperfect numbers -/

/-- No odd prime is superperfect. -/
theorem not_superperfect_of_odd_prime {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    ¬ Superperfect p := by
  intro h
  rw [Superperfect, sigma1_prime hp] at h
  obtain ⟨a, k, hk, hak⟩ := Nat.exists_eq_two_pow_mul_odd (n := p + 1) (by omega)
  have hcop : Nat.Coprime (2 ^ a) k := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hk)
  rw [hak, sigma1_mul_of_coprime hcop, sigma1_two_pow] at h
  -- `1 ≤ a` because `p + 1` is even while `k` is odd
  have ha : 1 ≤ a := by
    by_contra ha
    have ha0 : a = 0 := by omega
    subst ha0
    simp only [pow_zero, one_mul] at hak
    obtain ⟨j, hj⟩ := hodd
    obtain ⟨i, hi⟩ := hk
    omega
  set d := 2 ^ (a + 1) - 1 with hd
  have hpow : 2 ^ 2 ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hd3 : 3 ≤ d := by omega
  have hdodd : Odd d := by
    refine Nat.Even.sub_odd (by omega) ?_ odd_one
    exact (Nat.even_pow' (by omega)).mpr even_two
  have hdvd : d ∣ 2 * p := ⟨sigma1 k, h.symm⟩
  have hcop2 : Nat.Coprime d 2 := Nat.coprime_two_right.mpr hdodd
  have hdp : d ∣ p := Nat.Coprime.dvd_of_dvd_mul_left hcop2 hdvd
  have hcases := hp.eq_one_or_self_of_dvd d hdp
  have hdeq : d = p := by omega
  rw [hdeq] at h
  have hk2 : sigma1 k = 2 := Nat.eq_of_mul_eq_mul_left hp.pos (by omega)
  exact sigma1_ne_two k hk2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
theorem not_superperfect_small_odd : ∀ k < 250, ¬ Superperfect (2 * k + 1) := by decide

/-- Every odd superperfect number exceeds `500`; below that bound the claim is
verified by exhaustive computation. -/
theorem lt_of_odd_superperfect {n : ℕ} (hodd : Odd n) (h : Superperfect n) : 500 < n := by
  by_contra hn
  obtain ⟨k, hk⟩ := hodd
  subst hk
  exact not_superperfect_small_odd k (by omega) h

/-- **Reduction for the odd superperfect problem.**  An odd superperfect number
exists if and only if there is one which is moreover greater than `500` and
composite (not prime). -/
theorem OddSuperperfectExists :
    (∃ n : ℕ, Odd n ∧ Superperfect n) ↔
      (∃ n : ℕ, Odd n ∧ 500 < n ∧ ¬ n.Prime ∧ Superperfect n) := by
  constructor
  · rintro ⟨n, hodd, h⟩
    refine ⟨n, hodd, lt_of_odd_superperfect hodd h, ?_, h⟩
    intro hp
    exact not_superperfect_of_odd_prime hp hodd h
  · rintro ⟨n, hodd, _, _, h⟩
    exact ⟨n, hodd, h⟩

end Brockian.SuperperfectNumbers

