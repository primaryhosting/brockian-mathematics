/-
# No Pair Of Mersenne And Shifted Prime
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.no_pair_of_mersenne_and_shifted_prime
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open scoped ArithmeticFunction.sigma

namespace Brockian
namespace BetrothedNumbers

/-- Two natural numbers `m` and `n` form a *betrothed* (quasi-amicable) pair when the sum of
divisors of each of them equals `m + n + 1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  σ 1 m = m + n + 1 ∧ σ 1 n = m + n + 1

/-- The sum of divisors of a power of two. -/
theorem sigma_one_two_pow (k : ℕ) : σ 1 (2 ^ k) + 1 = 2 ^ (k + 1) := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [pow_succ, pow_succ] at *
      omega

/-- The sum of divisors of a prime. -/
theorem sigma_one_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  have h := ArithmeticFunction.sigma_one_apply_prime_pow (p := p) (i := 1) hp
  simpa [Finset.sum_range_succ, add_comm] using h

/-- The sum of divisors of the square of a prime. -/
theorem sigma_one_prime_sq {p : ℕ} (hp : p.Prime) : σ 1 (p ^ 2) = 1 + p + p ^ 2 := by
  have h := ArithmeticFunction.sigma_one_apply_prime_pow (p := p) (i := 2) hp
  simpa [Finset.sum_range_succ] using h

/-- The sum of divisors of a product of two distinct primes. -/
theorem sigma_one_mul_of_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    σ 1 (p * q) = (p + 1) * (q + 1) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
    sigma_one_prime hp, sigma_one_prime hq]

/-- The sum of divisors of `2 ^ k * p` for an odd prime `p`. -/
theorem sigma_one_two_pow_mul_odd_prime {k p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    σ 1 (2 ^ k * p) = (2 ^ (k + 1) - 1) * (p + 1) := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.even_iff_not_odd.mp (by decide)) hodd
  have hcop : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_prime hp]
  have h := sigma_one_two_pow k
  omega

/-- **Unique partner.** If `m` forms a betrothed pair with `2 ^ k * p` (`p` an odd prime),
then `m = (2 ^ k - 1) * (p + 2)`. -/
theorem unique_partner {k p m : ℕ} (hk : 2 ≤ k) (hp : p.Prime) (hodd : Odd p)
    (h : IsBetrothedPair (2 ^ k * p) m) : m = (2 ^ k - 1) * (p + 2) := by
  obtain ⟨h1, -⟩ := h
  rw [sigma_one_two_pow_mul_odd_prime hp hodd] at h1
  have hQ : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have hk4 : 4 ≤ 2 ^ k := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  set Q : ℕ := 2 ^ k with hQdef
  have hexp : (2 * Q - 1) * (p + 1) = 2 * Q * p + 2 * Q - p - 1 := by
    cases Nat.exists_eq_add_of_le (show 1 ≤ 2 * Q by omega) with
    | intro c hc =>
        have : 2 * Q = c + 1 := by omega
        rw [this]
        simp only [Nat.add_sub_cancel]
        ring_nf
        omega
  have hexp2 : (Q - 1) * (p + 2) = Q * p + 2 * Q - p - 2 := by
    cases Nat.exists_eq_add_of_le (show 1 ≤ Q by omega) with
    | intro c hc =>
        have : Q = c + 1 := by omega
        rw [this]
        simp only [Nat.add_sub_cancel]
        ring_nf
        omega
  rw [hQ, hexp] at h1
  rw [hexp2]
  have hQp : Q ≤ Q * p := Nat.le_mul_of_pos_right _ hp.pos
  omega

/-- **Target.** Let `k ≥ 2` and let `p` be an odd prime such that both `2 ^ k - 1` and `p + 2`
are prime.  Then no natural number forms a betrothed pair with `2 ^ k * p`. -/
theorem no_pair_of_mersenne_and_shifted_prime {k p : ℕ} (hk : 2 ≤ k) (hp : p.Prime)
    (hodd : Odd p) (hmers : (2 ^ k - 1).Prime) (hshift : (p + 2).Prime) :
    ¬ ∃ m : ℕ, IsBetrothedPair (2 ^ k * p) m := by
  rintro ⟨m, hm⟩
  have hmval : m = (2 ^ k - 1) * (p + 2) := unique_partner hk hp hodd hm
  obtain ⟨h1, h2⟩ := hm
  have hk4 : 4 ≤ 2 ^ k := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hp3 : 3 ≤ p := by
    rcases hp.eq_one_or_self_of_dvd 2 with _ | _
    · omega
    · rcases hp.two_le.lt_or_eq with h | h
      · omega
      · exact absurd (h ▸ (by decide : Odd 2)) (by simp)
  -- notation
  obtain ⟨q, hqdef⟩ : ∃ q : ℕ, 2 ^ k = q + 1 := ⟨2 ^ k - 1, by omega⟩
  have hqprime : q.Prime := by
    have : 2 ^ k - 1 = q := by omega
    rwa [this] at hmers
  have hq3 : 3 ≤ q := by omega
  -- the value of m
  have hm' : m = q * (p + 2) := by
    rw [hmval]
    congr 1
    omega
  -- the equation σ 1 m = 2^k*p + m + 1
  by_cases hcase : q = p + 2
  · -- m = q ^ 2
    have hmsq : m = q ^ 2 := by rw [hm', ← hcase]; ring
    rw [hmsq, sigma_one_prime_sq hqprime] at h2
    rw [hmsq] at h2
    have hQp : (q + 1) * p ≥ q + 1 := Nat.le_mul_of_pos_right _ (by omega)
    rw [hqdef] at h2
    omega
  · have hsig : σ 1 m = (q + 1) * (p + 3) := by
      rw [hm', sigma_one_mul_of_primes hqprime hshift hcase]
      ring
    rw [hsig, hm', hqdef] at h2
    nlinarith [h2, hq3, hp3]

end BetrothedNumbers
end Brockian

