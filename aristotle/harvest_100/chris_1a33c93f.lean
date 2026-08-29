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

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: they are distinct positive
integers each of whose sum of divisors equals `m + n + 1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigma 1 m = m + n + 1 ∧ sigma 1 n = m + n + 1

/-- Sanity check: `(48, 75)` is the smallest betrothed pair, so the definition is not vacuous. -/
example : IsBetrothedPair 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;>
    · rw [sigma_one_apply]; decide

/-- The sum of divisors of a prime. -/
theorem sigma_one_prime {p : ℕ} (hp : Nat.Prime p) : sigma 1 p = p + 1 := by
  rw [show p = p ^ 1 by ring, sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ, add_comm]

/-- The sum of divisors of the square of a prime. -/
theorem sigma_one_prime_sq {p : ℕ} (hp : Nat.Prime p) :
    sigma 1 (p * p) = 1 + p + p * p := by
  rw [show p * p = p ^ 2 by ring, sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]

/-- The sum of divisors of a power of two. -/
theorem sigma_one_two_pow (i : ℕ) : sigma 1 (2 ^ i) + 1 = 2 ^ (i + 1) := by
  rw [sigma_one_apply_prime_pow Nat.prime_two]
  induction i with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      ring_nf
      ring_nf at ih
      omega

/-- The sum of divisors of a product of two distinct primes. -/
theorem sigma_one_mul_of_coprime {a b : ℕ} (h : Nat.Coprime a b) :
    sigma 1 (a * b) = sigma 1 a * sigma 1 b :=
  isMultiplicative_sigma.map_mul_of_coprime h

/-- The sum of divisors of `2 ^ k * p` for an odd prime `p`, expressed via `q = 2 ^ k - 1`. -/
theorem sigma_one_two_pow_mul_prime {k p q : ℕ} (hp : Nat.Prime p) (hodd : Odd p)
    (hq : 2 ^ k = q + 1) : sigma 1 (2 ^ k * p) = (2 * q + 1) * (p + 1) := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hodd
  have hcop : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).mpr (fun h => hp2 h.symm))
  rw [sigma_one_mul_of_coprime hcop, sigma_one_prime hp]
  have h2 := sigma_one_two_pow k
  rw [show (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 by ring] at h2
  have hs : sigma 1 (2 ^ k) = 2 * q + 1 := by omega
  rw [hs]

/-- **Unique partner.** If `m` forms a betrothed pair with `2 ^ k * p` (`p` an odd prime),
then necessarily `m = (2 ^ k - 1) * (p + 2)`. -/
theorem unique_partner {k p m q : ℕ} (hp : Nat.Prime p) (hodd : Odd p)
    (hq : 2 ^ k = q + 1) (h : IsBetrothedPair m (2 ^ k * p)) :
    m = q * (p + 2) := by
  obtain ⟨-, -, -, -, hn⟩ := h
  rw [sigma_one_two_pow_mul_prime hp hodd hq, hq] at hn
  nlinarith [hn]

/-- **Main theorem.** Let `k ≥ 2` and let `p` be an odd prime. If `2 ^ k - 1` and `p + 2`
are both prime, then no `m` forms a betrothed pair with `2 ^ k * p`. -/
theorem no_pair_of_mersenne_and_shifted_prime {k p : ℕ} (hk : 2 ≤ k)
    (hp : Nat.Prime p) (hodd : Odd p) (hmer : Nat.Prime (2 ^ k - 1))
    (hshift : Nat.Prime (p + 2)) (m : ℕ) : ¬ IsBetrothedPair m (2 ^ k * p) := by
  intro hpair
  -- notation: `q = 2 ^ k - 1`
  set q : ℕ := 2 ^ k - 1 with hqdef
  have hpow : (4 : ℕ) ≤ 2 ^ k := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hq : 2 ^ k = q + 1 := by omega
  have hq3 : 3 ≤ q := by omega
  have hp3 : 3 ≤ p := by
    obtain ⟨t, ht⟩ := hodd
    have := hp.two_le
    omega
  have hm : m = q * (p + 2) := unique_partner hp hodd hq hpair
  obtain ⟨-, -, -, hsm, -⟩ := hpair
  rw [hm, hq] at hsm
  by_cases hcase : q = p + 2
  · -- the two auxiliary primes coincide: `m = q ^ 2`
    rw [hcase] at hsm
    rw [sigma_one_prime_sq hshift] at hsm
    nlinarith [hsm]
  · -- distinct primes
    have hcop : Nat.Coprime q (p + 2) := (Nat.coprime_primes hmer hshift).mpr hcase
    rw [sigma_one_mul_of_coprime hcop, sigma_one_prime hmer, sigma_one_prime hshift] at hsm
    nlinarith [hsm]

end BetrothedNumbers
end Brockian

