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

set_option grind.warning false

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers

/-- `n` and `m` form a *betrothed* (quasi-amicable) pair: they are distinct positive integers
whose sums of divisors both equal `n + m + 1`. -/
def IsBetrothedPair (n m : ℕ) : Prop :=
  0 < n ∧ 0 < m ∧ n ≠ m ∧ σ 1 n = n + m + 1 ∧ σ 1 m = n + m + 1

section Sigma

/-- The sum of divisors of a prime. -/
theorem sigma_one_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  have := ArithmeticFunction.sigma_one_apply_prime_pow (p := p) (i := 1) hp
  simp [Finset.sum_range_succ] at this
  simpa [add_comm] using this

/-- The sum of divisors of a power of two. -/
theorem sigma_one_two_pow (k : ℕ) : σ 1 (2 ^ k) + 1 = 2 * 2 ^ k := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
  induction k with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ]; ring_nf; ring_nf at ih; omega

/-- The sum of divisors of the square of a prime. -/
theorem sigma_one_prime_sq {q : ℕ} (hq : q.Prime) : σ 1 (q ^ 2) = 1 + q + q ^ 2 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hq]
  simp [Finset.sum_range_succ]

/-- The sum of divisors of a product of two distinct primes. -/
theorem sigma_one_mul_of_distinct_primes {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (h : q ≠ r) :
    σ 1 (q * r) = (q + 1) * (r + 1) := by
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
    ((Nat.coprime_primes hq hr).mpr h)]
  rw [sigma_one_prime hq, sigma_one_prime hr]

/-- The sum of divisors of `2 ^ k * p` for `p` an odd prime. -/
theorem sigma_one_two_pow_mul_odd_prime {k p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    σ 1 (2 ^ k * p) = (2 * 2 ^ k - 1) * (p + 1) := by
  have hcop : Nat.Coprime (2 ^ k) p := by
    refine Nat.Coprime.pow_left _ ?_
    have : ¬ (2 ∣ p) := by
      rw [Nat.two_dvd_ne_zero]
      simpa [Nat.odd_iff] using hodd
    simpa [Nat.coprime_primes Nat.prime_two hp, Nat.coprime_comm] using
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr this
  have h2 : σ 1 (2 ^ k) = 2 * 2 ^ k - 1 := by have := sigma_one_two_pow k; omega
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_prime hp, h2]

end Sigma

/-- **Unique partner.** If `2 ^ k * p` (with `k ≥ 2`, `p` an odd prime) forms a betrothed pair
with `m`, then `m = (2 ^ k - 1) * (p + 2)`. -/
theorem unique_partner {k p m : ℕ} (hk : 2 ≤ k) (hp : p.Prime) (hodd : Odd p)
    (h : IsBetrothedPair (2 ^ k * p) m) : m = (2 ^ k - 1) * (p + 2) := by
  obtain ⟨-, -, -, hn, -⟩ := h
  rw [sigma_one_two_pow_mul_odd_prime hp hodd] at hn
  have hA : 4 ≤ 2 ^ k := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  obtain ⟨B, hB⟩ : ∃ B, 2 ^ k = B + 1 := ⟨2 ^ k - 1, by omega⟩
  rw [hB] at hn ⊢
  have hn' : 2 * (B * p) + 2 * B + p + 1 = B * p + p + m + 1 := by
    have : (2 * (B + 1) - 1) * (p + 1) = 2 * (B * p) + 2 * B + p + 1 := by
      have : 2 * (B + 1) - 1 = 2 * B + 1 := by omega
      rw [this]; ring
    rw [this] at hn
    calc 2 * (B * p) + 2 * B + p + 1 = (B + 1) * p + m + 1 := hn
    _ = B * p + p + m + 1 := by ring
  have : m = B * p + 2 * B := by omega
  rw [this]
  simp only [Nat.add_sub_cancel]
  ring

/-- **Target.** Let `k ≥ 2` and let `p` be an odd prime.  If both `2 ^ k - 1` and `p + 2` are
prime, then no number forms a betrothed pair with `2 ^ k * p`. -/
theorem no_pair_of_mersenne_and_shifted_prime {k p : ℕ} (hk : 2 ≤ k) (hp : p.Prime)
    (hodd : Odd p) (hq : Nat.Prime (2 ^ k - 1)) (hr : Nat.Prime (p + 2)) :
    ¬ ∃ m, IsBetrothedPair (2 ^ k * p) m := by
  rintro ⟨m, hm⟩
  have hmval : m = (2 ^ k - 1) * (p + 2) := unique_partner hk hp hodd hm
  obtain ⟨-, -, -, -, hσm⟩ := hm
  have hA : 4 ≤ 2 ^ k := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hp2 : p ≠ 2 := by
    rintro rfl
    simp [Nat.odd_iff] at hodd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨B, hBA⟩ : ∃ B, 2 ^ k = B + 1 := ⟨2 ^ k - 1, by omega⟩
  have hB3 : 3 ≤ B := by omega
  have hBsub : 2 ^ k - 1 = B := by omega
  rw [hBsub] at hmval hq
  rw [hmval, hBA] at hσm
  by_cases hqr : B = p + 2
  · -- the two auxiliary primes coincide: `m` is a prime square
    rw [hqr, show (p + 2) * (p + 2) = (p + 2) ^ 2 by ring, sigma_one_prime_sq hr] at hσm
    nlinarith [hσm, hp3]
  · -- distinct auxiliary primes
    rw [sigma_one_mul_of_distinct_primes hq hr hqr] at hσm
    nlinarith [hσm, hp3, hB3]

/-- Sanity check: the definition is not vacuous — `(48, 75)` is a betrothed pair. -/
theorem isBetrothedPair_48_75 : IsBetrothedPair 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;>
    simp [ArithmeticFunction.sigma_one_apply, Nat.divisors] <;> decide

/-- Sanity check: the hypotheses of the target theorem are satisfiable (`k = 2`, `p = 3`),
so the statement is not vacuous. -/
theorem no_pair_twelve : ¬ ∃ m, IsBetrothedPair (2 ^ 2 * 3) m :=
  no_pair_of_mersenne_and_shifted_prime (k := 2) (p := 3) (by norm_num) (by norm_num)
    (by decide) (by norm_num) (by norm_num)

end Brockian.BetrothedNumbers

