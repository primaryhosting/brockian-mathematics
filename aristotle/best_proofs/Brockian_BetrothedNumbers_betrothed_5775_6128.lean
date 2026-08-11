/-
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Betrothed 5775 6128
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.betrothed_5775_6128
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction

namespace Brockian.BetrothedNumbers

/-- `IsBetrothedPair a b` states that `a` and `b` form a betrothed (quasi-amicable) pair:
two distinct positive integers each of whose sum of divisors equals `a + b + 1`. -/
def IsBetrothedPair (a b : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ a ≠ b ∧ sigma 1 a = a + b + 1 ∧ sigma 1 b = a + b + 1

/-- `σ₁(2^k) = 2^(k+1) - 1`. -/
theorem sigma_one_two_pow (k : ℕ) : sigma 1 (2 ^ k) = 2 ^ (k + 1) - 1 := by
  rw [sigma_one_apply, Nat.sum_divisors_prime_pow Nat.prime_two]
  simp [Nat.geomSum_eq]

/-- `σ₁(p) = p + 1` for a prime `p`. -/
theorem sigma_one_prime {p : ℕ} (hp : p.Prime) : sigma 1 p = p + 1 := by
  rw [sigma_one_apply, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  omega

/-- The sigma value of `2^k * p` for an odd prime `p`. -/
theorem sigma_one_two_pow_mul_prime {k p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    sigma 1 (2 ^ k * p) = (2 ^ (k + 1) - 1) * (p + 1) := by
  have hcop : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hodd))
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_two_pow, sigma_one_prime hp]

/-- **The `2^k · p` sigma criterion for betrothed pairs.**
If `p` is an odd prime, `a` is a positive number distinct from `b = 2^k * p` with
`σ₁(a) = a + b + 1`, and the closed-form value `(2^(k+1) - 1)(p + 1)` of `σ₁(b)` also
equals `a + b + 1`, then `(a, b)` is a betrothed pair. -/
theorem isBetrothedPair_of_sigma_criterion {k p a : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (ha : 0 < a) (hne : a ≠ 2 ^ k * p) (h1 : sigma 1 a = a + 2 ^ k * p + 1)
    (h2 : (2 ^ (k + 1) - 1) * (p + 1) = a + 2 ^ k * p + 1) :
    IsBetrothedPair a (2 ^ k * p) := by
  refine ⟨ha, Nat.mul_pos (Nat.two_pow_pos k) hp.pos, hne, h1, ?_⟩
  rw [sigma_one_two_pow_mul_prime hp hodd, h2]

set_option maxRecDepth 100000 in
/-- Kernel-checked value of `σ₁(5775)`. -/
theorem sigma_one_5775 : sigma 1 5775 = 11904 := by
  rw [sigma_one_apply]
  decide

set_option maxRecDepth 100000 in
/-- Kernel-checked value of `σ₁(6128)`. -/
theorem sigma_one_6128 : sigma 1 6128 = 11904 := by
  rw [sigma_one_apply]
  decide

/-- **5775 and 6128 form a betrothed (quasi-amicable) pair.** -/
theorem betrothed_5775_6128 : IsBetrothedPair 5775 6128 :=
  ⟨by norm_num, by norm_num, by norm_num, by rw [sigma_one_5775], by rw [sigma_one_6128]⟩

/-- The pair `(5775, 6128)` arises from the sigma criterion with `k = 4`, `p = 383`:
`6128 = 2^4 · 383` and `σ₁(6128) = (2^5 - 1)(383 + 1) = 11904 = 5775 + 6128 + 1`. -/
theorem betrothed_5775_6128_via_criterion :
    IsBetrothedPair 5775 (2 ^ 4 * 383) := by
  refine isBetrothedPair_of_sigma_criterion (k := 4) (p := 383) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_ (by norm_num)
  rw [sigma_one_5775]
  norm_num

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

