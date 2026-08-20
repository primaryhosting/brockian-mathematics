import Mathlib

/-!
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-- The sum of all (positive) divisors of `n`, i.e. `σ₁ n`. -/
def sigmaSum (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: they are distinct positive integers
each of whose divisor sums equals `m + n + 1`, i.e. the sum of the *proper* divisors of each
(excluding `1` and the number itself) equals the other number. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigmaSum m = m + n + 1 ∧ sigmaSum n = m + n + 1

lemma sigmaSum_eq_sigma_one (n : ℕ) : sigmaSum n = sigma 1 n := (sigma_one_apply n).symm

/-- `σ₁ (2 ^ k) = 2 ^ (k + 1) - 1`. -/
lemma sigmaSum_two_pow (k : ℕ) : sigmaSum (2 ^ k) = 2 ^ (k + 1) - 1 := by
  unfold sigmaSum
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have : 2 ≤ 2 ^ (n + 1) := Nat.one_lt_two_pow (by omega)
      ring_nf
      omega

/-- `σ₁ (2 ^ k * p) = (2 ^ (k + 1) - 1) * (p + 1)` for an odd prime `p`. -/
lemma sigmaSum_two_pow_mul_prime (k p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    sigmaSum (2 ^ k * p) = (2 ^ (k + 1) - 1) * (p + 1) := by
  have hcop : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  rw [sigmaSum_eq_sigma_one, isMultiplicative_sigma.map_mul_of_coprime hcop,
    ← sigmaSum_eq_sigma_one, ← sigmaSum_eq_sigma_one, sigmaSum_two_pow]
  unfold sigmaSum
  rw [hp.sum_divisors]

/-- **Key intermediate lemma (the `σ` criterion).**  If `p` is an odd prime, `m` is a positive
integer different from `2 ^ k * p`, and both `σ₁ m` and `m + 2 ^ k * p + 1` equal
`(2 ^ (k + 1) - 1) * (p + 1) = σ₁ (2 ^ k * p)`, then `(m, 2 ^ k * p)` is a betrothed pair. -/
lemma betrothed_of_sigma_criterion {k p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 0 < m)
    (hne : m ≠ 2 ^ k * p) (hsm : sigmaSum m = (2 ^ (k + 1) - 1) * (p + 1))
    (hsum : m + 2 ^ k * p + 1 = (2 ^ (k + 1) - 1) * (p + 1)) :
    IsBetrothedPair m (2 ^ k * p) := by
  refine ⟨hm, ?_, hne, ?_, ?_⟩
  · exact Nat.mul_pos (Nat.two_pow_pos k) hp.pos
  · rw [hsm, hsum]
  · rw [sigmaSum_two_pow_mul_prime k p hp hp2, hsum]

set_option maxRecDepth 100000 in
/-- `σ₁ 5775 = 11904`. -/
lemma sigmaSum_5775 : sigmaSum 5775 = 11904 := by
  unfold sigmaSum
  decide

set_option maxRecDepth 100000 in
/-- `σ₁ 6128 = 11904`. -/
lemma sigmaSum_6128 : sigmaSum 6128 = 11904 := by
  unfold sigmaSum
  decide

/-- **`(5775, 6128)` is a betrothed (quasi-amicable) pair.** -/
theorem betrothed_5775_6128 : IsBetrothedPair 5775 6128 := by
  have h6128 : (6128 : ℕ) = 2 ^ 4 * 383 := by norm_num
  have hp : Nat.Prime 383 := by norm_num
  rw [h6128]
  refine betrothed_of_sigma_criterion hp (by norm_num) (by norm_num) (by norm_num) ?_ (by norm_num)
  rw [sigmaSum_5775]
  norm_num

/-- The pair `(5775, 6128)` is the one produced by the `σ` criterion with `k = 4` and `p = 383`:
`383` is an odd prime, `6128 = 2 ^ 4 * 383`, and
`σ₁ 5775 = σ₁ (2 ^ 4 * 383) = (2 ^ 5 - 1) * (383 + 1) = 5775 + 6128 + 1`. -/
theorem betrothed_5775_6128_sigma_criterion :
    Nat.Prime 383 ∧ (383 : ℕ) ≠ 2 ∧ (6128 : ℕ) = 2 ^ 4 * 383 ∧
      sigmaSum (2 ^ 4 * 383) = (2 ^ (4 + 1) - 1) * (383 + 1) ∧
      sigmaSum 5775 = (2 ^ (4 + 1) - 1) * (383 + 1) ∧
      5775 + 2 ^ 4 * 383 + 1 = (2 ^ (4 + 1) - 1) * (383 + 1) := by
  have hp : Nat.Prime 383 := by norm_num
  refine ⟨hp, by norm_num, by norm_num, ?_, ?_, by norm_num⟩
  · rw [sigmaSum_two_pow_mul_prime 4 383 hp (by norm_num)]
  · rw [sigmaSum_5775]; norm_num

/-- Cross-check: the criterion value agrees with the direct kernel computation of `σ₁ 6128`. -/
lemma sigmaSum_6128_eq_criterion :
    sigmaSum 6128 = (2 ^ (4 + 1) - 1) * (383 + 1) := by
  rw [sigmaSum_6128]; norm_num

end Brockian.BetrothedNumbers

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

