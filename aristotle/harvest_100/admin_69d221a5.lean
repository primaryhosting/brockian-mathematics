/-
# No Pair Of Mersenne And Shifted Prime
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.no_pair_of_mersenne_and_shifted_prime
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# No Pair Of Mersenne And Shifted Prime
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.no_pair_of_mersenne_and_shifted_prime
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian
namespace BetrothedNumbers

/-- Two distinct positive naturals `m` and `n` form a *betrothed* (quasi-amicable) pair when
each one's sum of divisors equals `m + n + 1`, i.e. the sum of the proper divisors of each
(excluding `1` and the number itself) equals the other number. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ σ 1 m = m + n + 1 ∧ σ 1 n = m + n + 1

/-- Geometric sum of powers of two. -/
lemma sum_range_two_pow (n : ℕ) : ∑ i ∈ Finset.range (n + 1), 2 ^ i = 2 ^ (n + 1) - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have : (1 : ℕ) ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
      have : (2 : ℕ) ^ (n + 2) = 2 ^ (n + 1) * 2 := by ring
      omega

/-- `σ₁` of a power of two. -/
lemma sigma_one_two_pow (k : ℕ) : σ 1 (2 ^ k) = 2 ^ (k + 1) - 1 := by
  rw [sigma_one_apply_prime_pow Nat.prime_two, sum_range_two_pow]

/-- `σ₁` of a prime. -/
lemma sigma_one_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  have := sigma_one_apply_prime_pow (i := 1) hp
  simpa [Finset.sum_range_succ, add_comm] using this

/-- `σ₁` of the square of a prime. -/
lemma sigma_one_prime_sq {p : ℕ} (hp : p.Prime) : σ 1 (p ^ 2) = 1 + p + p ^ 2 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]

/-- `σ₁` of a product of two distinct primes. -/
lemma sigma_one_mul_distinct_primes {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r) :
    σ 1 (q * r) = (q + 1) * (r + 1) := by
  have hcop : Nat.gcd q r = 1 := (Nat.coprime_primes hq hr).2 hqr
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_prime hq, sigma_one_prime hr]

/-- `σ₁` of `2 ^ k * p` for an odd prime `p`. -/
lemma sigma_one_two_pow_mul_prime {k p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    σ 1 (2 ^ k * p) = (2 ^ (k + 1) - 1) * (p + 1) := by
  have hcop : Nat.gcd (2 ^ k) p = 1 := by
    have h2p : (2 : ℕ) ≠ p := by
      rintro rfl
      simp [Nat.odd_iff] at hodd
    exact Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).2 h2p)
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_two_pow, sigma_one_prime hp]

/-- **Unique partner.** If `m` forms a betrothed pair with `2 ^ k * p` (`p` an odd prime),
then `m = (2 ^ k - 1) * (p + 2)`. -/
theorem partner_eq {k p m : ℕ} (hp : p.Prime) (hodd : Odd p)
    (h : IsBetrothedPair m (2 ^ k * p)) : m = (2 ^ k - 1) * (p + 2) := by
  obtain ⟨-, -, -, -, hσn⟩ := h
  rw [sigma_one_two_pow_mul_prime hp hodd] at hσn
  obtain ⟨u, hu⟩ : ∃ u, 2 ^ k = u + 1 := ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
  have key : (2 ^ k - 1) * (p + 2) + 2 ^ k * p + 1 = (2 ^ (k + 1) - 1) * (p + 1) := by
    have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [h2, hu]
    have : 2 * (u + 1) - 1 = 2 * u + 1 := by omega
    rw [this]
    simp only [Nat.add_sub_cancel]
    ring
  omega

/-- **Target.** For `k ≥ 2` and an odd prime `p` such that `2 ^ k - 1` and `p + 2` are both
prime, no natural number forms a betrothed pair with `2 ^ k * p`. -/
theorem no_pair_of_mersenne_and_shifted_prime {k p : ℕ} (hk : 2 ≤ k) (hp : p.Prime) (hodd : Odd p)
    (hq : (2 ^ k - 1).Prime) (hr : (p + 2).Prime) :
    ¬ ∃ m, IsBetrothedPair m (2 ^ k * p) := by
  rintro ⟨m, hm⟩
  have hmeq : m = (2 ^ k - 1) * (p + 2) := partner_eq hp hodd hm
  obtain ⟨-, -, -, hσm, hσn⟩ := hm
  -- both sigmas agree
  have hEq : σ 1 m = σ 1 (2 ^ k * p) := by rw [hσm, hσn]
  rw [sigma_one_two_pow_mul_prime hp hodd] at hEq
  -- notation
  have ht4 : (4 : ℕ) ≤ 2 ^ k := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    have := Nat.odd_iff.mp hodd
    omega
  have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
  obtain ⟨u, hu⟩ : ∃ u, 2 ^ k = u + 4 := ⟨2 ^ k - 4, by omega⟩
  by_cases hcase : (2 ^ k - 1) = p + 2
  · -- `m` is the square of a prime
    have hmsq : m = (2 ^ k - 1) ^ 2 := by rw [hmeq, ← hcase]; ring
    rw [hmsq, sigma_one_prime_sq hq, h2, hu] at hEq
    have h1 : u + 4 - 1 = u + 3 := by omega
    have h2' : 2 * (u + 4) - 1 = 2 * u + 7 := by omega
    rw [h1, h2'] at hEq
    have hpu : p = u + 1 := by omega
    rw [hpu] at hEq
    nlinarith [hEq]
  · -- `m` is a product of two distinct primes
    rw [hmeq, sigma_one_mul_distinct_primes hq hr hcase, h2, hu] at hEq
    have h1 : u + 4 - 1 = u + 3 := by omega
    have h2' : 2 * (u + 4) - 1 = 2 * u + 7 := by omega
    rw [h1, h2'] at hEq
    nlinarith [hEq, hp3]

end BetrothedNumbers
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

