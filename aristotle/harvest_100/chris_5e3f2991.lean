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
# No Pair Of Mersenne And Shifted Prime
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.no_pair_of_mersenne_and_shifted_prime
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers

/-- Two natural numbers form a *betrothed* (quasi-amicable) pair when the sum of the
divisors of each of them equals the sum of the two numbers plus one. -/
def IsBetrothedPair (n m : ℕ) : Prop :=
  σ 1 n = n + m + 1 ∧ σ 1 m = n + m + 1

/-- `σ 1 p = p + 1` for a prime `p`. -/
lemma sigma_one_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  have h := ArithmeticFunction.sigma_one_apply_prime_pow (p := p) (i := 1) hp
  simpa [Finset.sum_range_succ, Nat.add_comm] using h

/-- `σ 1 (p * q) = (p + 1) * (q + 1)` for distinct primes `p, q`. -/
lemma sigma_one_mul_of_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    σ 1 (p * q) = (p + 1) * (q + 1) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
    sigma_one_prime hp, sigma_one_prime hq]

/-- `σ 1 (p ^ 2) = p ^ 2 + p + 1` for a prime `p`. -/
lemma sigma_one_prime_sq {p : ℕ} (hp : p.Prime) : σ 1 (p ^ 2) = p ^ 2 + p + 1 := by
  have h := ArithmeticFunction.sigma_one_apply_prime_pow (p := p) (i := 2) hp
  rw [h]
  simp [Finset.sum_range_succ]
  ring

/-- The geometric sum: `σ 1 (2 ^ k) + 1 = 2 ^ (k + 1)`. -/
lemma sigma_one_two_pow (k : ℕ) : σ 1 (2 ^ k) + 1 = 2 ^ (k + 1) := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [pow_succ 2 (n + 1)]
      omega

/-- `σ 1 (2 ^ k * p) + (p + 1) = 2 ^ (k + 1) * (p + 1)` for an odd prime `p`. -/
lemma sigma_one_two_pow_mul_odd_prime {k p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    σ 1 (2 ^ k * p) + (p + 1) = 2 ^ (k + 1) * (p + 1) := by
  have hp2 : (2 : ℕ) ≠ p := by
    rintro rfl
    obtain ⟨t, ht⟩ := hodd
    omega
  have hcop : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).mpr hp2)
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_prime hp]
  have h := sigma_one_two_pow k
  nlinarith [h]

/-- **Unique partner.** If `m` satisfies the first betrothed equation with `2 ^ k * p`
(for `p` an odd prime), then `m = (2 ^ k - 1) * (p + 2)`. -/
lemma partner_eq {k p m : ℕ} (hp : p.Prime) (hodd : Odd p)
    (h : σ 1 (2 ^ k * p) = 2 ^ k * p + m + 1) : m = (2 ^ k - 1) * (p + 2) := by
  have hs := sigma_one_two_pow_mul_odd_prime (k := k) hp hodd
  obtain ⟨q, hq⟩ : ∃ q, 2 ^ k = q + 1 := ⟨2 ^ k - 1, by
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega⟩
  rw [hq] at hs h ⊢
  have hpow : (2 : ℕ) ^ (k + 1) = 2 * (q + 1) := by rw [pow_succ, hq]; ring
  rw [hpow] at hs
  simp only [Nat.add_sub_cancel]
  rw [h] at hs
  nlinarith [hs]

/-- **Main result.** For `k ≥ 2` and an odd prime `p` such that both `2 ^ k - 1` and `p + 2`
are prime, the number `2 ^ k * p` is not part of any betrothed pair. -/
theorem no_pair_of_mersenne_and_shifted_prime {k p : ℕ} (hk : 2 ≤ k) (hp : p.Prime)
    (hodd : Odd p) (hM : Nat.Prime (2 ^ k - 1)) (hS : Nat.Prime (p + 2)) :
    ∀ m : ℕ, ¬ IsBetrothedPair (2 ^ k * p) m := by
  rintro m ⟨h1, h2⟩
  have hm : m = (2 ^ k - 1) * (p + 2) := partner_eq hp hodd h1
  -- notation
  obtain ⟨q, hq⟩ : ∃ q, 2 ^ k = q + 1 := ⟨2 ^ k - 1, by
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega⟩
  have hq3 : 3 ≤ q := by
    have h4 : (4 : ℕ) ≤ 2 ^ k := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  have hp3 : 3 ≤ p := by
    obtain ⟨t, ht⟩ := hodd
    have := hp.two_le
    omega
  have hMq : Nat.Prime q := by rw [hq] at hM; simpa using hM
  have hmq : m = q * (p + 2) := by rw [hm, hq]; simp
  by_cases hqr : q = p + 2
  · -- `m = q ^ 2`
    have hmsq : m = q ^ 2 := by rw [hmq, ← hqr]; ring
    rw [hmsq, sigma_one_prime_sq hMq, hq] at h2
    nlinarith [h2, hq3, hp3, hqr]
  · have := sigma_one_mul_of_primes hMq hS hqr
    rw [hmq, this, hq] at h2
    nlinarith [h2, hq3, hp3]

/-- Sanity check: `(48, 75)` is a betrothed pair. -/
example : IsBetrothedPair 48 75 := by
  constructor <;> decide

/-- Sanity check: the hypotheses of the main theorem are satisfiable
(`k = 2`, `p = 3`: `2 ^ 2 - 1 = 3` and `3 + 2 = 5` are prime). -/
example : (2 : ℕ) ≤ 2 ∧ Nat.Prime 3 ∧ Odd 3 ∧ Nat.Prime (2 ^ 2 - 1) ∧ Nat.Prime (3 + 2) := by
  refine ⟨le_rfl, by norm_num, by decide, by norm_num, by norm_num⟩

end Brockian.BetrothedNumbers

