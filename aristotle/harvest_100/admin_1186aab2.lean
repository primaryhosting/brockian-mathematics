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

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- `n` and `m` form a *betrothed* (quasi-amicable) pair: both are positive and each has
divisor sum equal to `n + m + 1`.  (Distinctness of `n` and `m`, which is part of the usual
definition, is *not* assumed here; omitting it only makes the non-existence result stronger.) -/
def IsBetrothedPair (n m : ℕ) : Prop :=
  0 < n ∧ 0 < m ∧ σ 1 n = n + m + 1 ∧ σ 1 m = n + m + 1

/-- The divisor sum of a prime. -/
lemma sigma_one_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  have h := ArithmeticFunction.sigma_one_apply_prime_pow (p := p) (i := 1) hp
  simp [Finset.sum_range_succ] at h
  simpa [add_comm] using h

/-- The divisor sum of a power of two. -/
lemma sigma_one_two_pow (i : ℕ) : σ 1 (2 ^ i) = 2 ^ (i + 1) - 1 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
  induction i with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have h : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
      ring_nf
      omega

/-- The divisor sum of `2 ^ k * p` for an odd prime `p`. -/
lemma sigma_one_two_pow_mul_odd_prime {k p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    σ 1 (2 ^ k * p) = (2 ^ (k + 1) - 1) * (p + 1) := by
  have hcop : Nat.Coprime (2 ^ k) p := by
    refine Nat.Coprime.pow_left _ ?_
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by
      have h2 := Nat.odd_iff.mp hodd
      omega)
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
    sigma_one_two_pow, sigma_one_prime hp]

/-- The divisor sum of a product of two distinct primes. -/
lemma sigma_one_prime_mul_prime {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hne : q ≠ r) :
    σ 1 (q * r) = (q + 1) * (r + 1) := by
  have hcop : Nat.Coprime q r := (Nat.coprime_primes hq hr).mpr hne
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
    sigma_one_prime hq, sigma_one_prime hr]

/-- The divisor sum of the square of a prime. -/
lemma sigma_one_prime_sq {q : ℕ} (hq : q.Prime) : σ 1 (q * q) = 1 + q + q * q := by
  have h := ArithmeticFunction.sigma_one_apply_prime_pow (p := q) (i := 2) hq
  rw [show q ^ 2 = q * q by ring] at h
  rw [h]
  simp [Finset.sum_range_succ]
  ring

/-- **Unique partner.**  If `m` forms a betrothed pair with `2 ^ k * p` (`p` an odd prime),
then necessarily `m = (2 ^ k - 1) * (p + 2)`. -/
lemma partner_eq {k p m : ℕ} (hp : p.Prime) (hodd : Odd p)
    (h : IsBetrothedPair (2 ^ k * p) m) : m = (2 ^ k - 1) * (p + 2) := by
  obtain ⟨-, -, hn, -⟩ := h
  rw [sigma_one_two_pow_mul_odd_prime hp hodd] at hn
  obtain ⟨b, hb⟩ : ∃ b : ℕ, 2 ^ k = b + 1 := ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
  have hb2 : 2 ^ (k + 1) - 1 = 2 * b + 1 := by rw [pow_succ]; omega
  rw [hb2, hb] at hn
  rw [hb]
  simp only [Nat.add_sub_cancel]
  nlinarith [hn]

/-- **Main result.**  Let `k ≥ 2` and let `p` be an odd prime such that both the Mersenne
number `2 ^ k - 1` and the shifted prime `p + 2` are prime.  Then no natural number `m`
forms a betrothed pair with `2 ^ k * p`. -/
theorem no_pair_of_mersenne_and_shifted_prime {k p : ℕ} (hk : 2 ≤ k) (hp : p.Prime)
    (hodd : Odd p) (hmer : Nat.Prime (2 ^ k - 1)) (hshift : Nat.Prime (p + 2)) (m : ℕ) :
    ¬ IsBetrothedPair (2 ^ k * p) m := by
  intro hpair
  have hm : m = (2 ^ k - 1) * (p + 2) := partner_eq hp hodd hpair
  obtain ⟨-, -, hn, hsm⟩ := hpair
  rw [sigma_one_two_pow_mul_odd_prime hp hodd] at hn
  rw [← hn] at hsm
  -- introduce `b` with `2 ^ k = b + 1`
  obtain ⟨b, hb⟩ : ∃ b : ℕ, 2 ^ k = b + 1 :=
    ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
  have hb3 : 3 ≤ b := by
    have h4 : (4 : ℕ) ≤ 2 ^ k := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  have hb2 : 2 ^ (k + 1) - 1 = 2 * b + 1 := by rw [pow_succ]; omega
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    have h3 := Nat.odd_iff.mp hodd
    omega
  have hmb : m = b * (p + 2) := by rw [hm, hb]; simp
  rw [hb] at hmer
  simp only [Nat.add_sub_cancel] at hmer
  by_cases hqr : b = p + 2
  · -- the two auxiliary primes coincide: `m` is the square of a prime
    have hmsq : m = b * b := by rw [hmb, hqr]
    rw [hmsq, sigma_one_prime_sq hmer, hb2, hqr] at hsm
    nlinarith [hsm, hp3]
  · -- distinct primes
    rw [hmb, sigma_one_prime_mul_prime hmer hshift hqr, hb2] at hsm
    nlinarith [hsm, hb3, hp3]

end Brockian.BetrothedNumbers

