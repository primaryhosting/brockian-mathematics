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

namespace Brockian.BetrothedNumbers

/-- The sum-of-divisors function `σ₁`. -/
def sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `n` and `m` form a *betrothed* (quasi-amicable) pair: the sum of the divisors of each of
them, excluding `1` and the number itself, equals the other number.  Equivalently
`σ₁ n = σ₁ m = n + m + 1`. -/
def IsBetrothedPair (n m : ℕ) : Prop :=
  0 < n ∧ 0 < m ∧ sigmaOne n = n + m + 1 ∧ sigmaOne m = n + m + 1

lemma sigmaOne_mul_of_coprime {a b : ℕ} (h : Nat.Coprime a b) :
    sigmaOne (a * b) = sigmaOne a * sigmaOne b := by
  simpa [sigmaOne] using Nat.Coprime.sum_divisors_mul h

lemma sigmaOne_prime {p : ℕ} (hp : p.Prime) : sigmaOne p = p + 1 := by
  have h1 : p ≠ 1 := hp.ne_one
  simp [sigmaOne, hp.divisors, Finset.sum_pair (Ne.symm h1), Nat.add_comm]

lemma sigmaOne_two_pow (k : ℕ) : sigmaOne (2 ^ k) + 1 = 2 ^ (k + 1) := by
  induction k with
  | zero => simp [sigmaOne]
  | succ n ih =>
      have hcalc : sigmaOne (2 ^ (n + 1)) = sigmaOne (2 ^ n) + 2 ^ (n + 1) := by
        simp only [sigmaOne, Nat.sum_divisors_prime_pow Nat.prime_two,
          Finset.sum_range_succ]
      rw [hcalc]
      have : 2 ^ (n + 1 + 1) = 2 ^ (n + 1) + 2 ^ (n + 1) := by ring
      omega

lemma sigmaOne_prime_sq {q : ℕ} (hq : q.Prime) : sigmaOne (q ^ 2) = 1 + q + q ^ 2 := by
  simp only [sigmaOne, Nat.sum_divisors_prime_pow hq]
  simp [Finset.sum_range_succ]

/-- **Unique partner.**  If `m` forms a betrothed pair with `2 ^ k * p` (`k ≥ 1`, `p` an odd
prime), then necessarily `m = (2 ^ k - 1) * (p + 2)`. -/
lemma unique_partner {k p q m : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hq : 2 ^ k = q + 1) (h : IsBetrothedPair (2 ^ k * p) m) :
    m = q * (p + 2) := by
  obtain ⟨-, -, hn, -⟩ := h
  have hp2 : p ≠ 2 := by
    rintro rfl
    simp [Nat.odd_iff] at hodd
  have hcop : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  rw [sigmaOne_mul_of_coprime hcop, sigmaOne_prime hp] at hn
  have h2 : sigmaOne (2 ^ k) + 1 = 2 ^ (k + 1) := sigmaOne_two_pow k
  have h2' : 2 ^ (k + 1) = 2 * (q + 1) := by
    rw [pow_succ, hq]; ring
  have hs : sigmaOne (2 ^ k) = 2 * q + 1 := by omega
  rw [hs, hq] at hn
  -- `hn : (2 * q + 1) * (p + 1) = (q + 1) * p + m + 1`
  have hexp : (2 * q + 1) * (p + 1) = 2 * (q * p) + 2 * q + p + 1 := by ring
  have hexp2 : (q + 1) * p = q * p + p := by ring
  have htgt : q * (p + 2) = q * p + 2 * q := by ring
  omega

/-- **Main theorem.**  Let `k ≥ 2` and let `p` be an odd prime.  If both `2 ^ k - 1` and `p + 2`
are prime, then no natural number `m` forms a betrothed pair with `2 ^ k * p`. -/
theorem no_pair_of_mersenne_and_shifted_prime {k p : ℕ} (hk : 2 ≤ k) (hp : p.Prime)
    (hodd : Odd p) (hmers : (2 ^ k - 1).Prime) (hshift : (p + 2).Prime) :
    ¬ ∃ m : ℕ, IsBetrothedPair (2 ^ k * p) m := by
  rintro ⟨m, hm⟩
  -- notation: `q = 2 ^ k - 1`, `r = p + 2`
  obtain ⟨q, hpow⟩ : ∃ q : ℕ, 2 ^ k = q + 1 :=
    ⟨2 ^ k - 1, by have : 1 ≤ 2 ^ k := Nat.one_le_two_pow; omega⟩
  have hq3 : 3 ≤ q := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  have hqprime : q.Prime := by
    have hqe : 2 ^ k - 1 = q := by omega
    rwa [hqe] at hmers
  have hp2 : p ≠ 2 := by
    rintro rfl
    simp [Nat.odd_iff] at hodd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hmval : m = q * (p + 2) := unique_partner hp hodd hpow hm
  obtain ⟨-, -, hn, hmm⟩ := hm
  -- the common value of `σ₁`
  have hcop : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have hsn : sigmaOne (2 ^ k * p) = (2 * q + 1) * (p + 1) := by
    rw [sigmaOne_mul_of_coprime hcop, sigmaOne_prime hp]
    have h2 : sigmaOne (2 ^ k) + 1 = 2 ^ (k + 1) := sigmaOne_two_pow k
    have h2' : 2 ^ (k + 1) = 2 * (q + 1) := by rw [pow_succ, hpow]; ring
    have : sigmaOne (2 ^ k) = 2 * q + 1 := by omega
    rw [this]
  rw [hsn] at hn
  rw [hmval] at hn hmm
  -- `hn : (2 * q + 1) * (p + 1) = 2 ^ k * p + q * (p + 2) + 1`
  by_cases hqr : q = p + 2
  · -- the two auxiliary primes coincide: `m = q ^ 2`
    have hsq : q * (p + 2) = q ^ 2 := by rw [← hqr]; ring
    rw [hsq, sigmaOne_prime_sq hqprime] at hmm
    -- `1 + q + q ^ 2 = (2 * q + 1) * (p + 1)` with `q = p + 2`
    have hkey : 1 + q + q ^ 2 = (2 * q + 1) * (p + 1) := by omega
    rw [hqr] at hkey
    nlinarith [hkey, hp3]
  · -- the two auxiliary primes are distinct: `m = q * (p + 2)` with `q ≠ p + 2`
    have hcop2 : Nat.Coprime q (p + 2) := (Nat.coprime_primes hqprime hshift).mpr hqr
    rw [sigmaOne_mul_of_coprime hcop2, sigmaOne_prime hqprime, sigmaOne_prime hshift] at hmm
    -- `(q + 1) * (p + 3) = (2 * q + 1) * (p + 1)`
    have hkey : (q + 1) * (p + 2 + 1) = (2 * q + 1) * (p + 1) := by omega
    have e1 : (q + 1) * (p + 2 + 1) = q * p + 3 * q + p + 3 := by ring
    have e2 : (2 * q + 1) * (p + 1) = 2 * (q * p) + 2 * q + p + 1 := by ring
    have hqp : 3 * q ≤ q * p := by nlinarith
    omega

end Brockian.BetrothedNumbers

