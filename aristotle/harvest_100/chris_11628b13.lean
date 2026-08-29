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
def sigma1 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `n` and `m` form a *betrothed* (quasi-amicable) pair: each is the sum of the
proper divisors of the other excluding `1`, equivalently
`σ(n) = σ(m) = n + m + 1`. -/
def IsBetrothedPair (n m : ℕ) : Prop :=
  sigma1 n = n + m + 1 ∧ sigma1 m = n + m + 1

lemma sigma1_prime {p : ℕ} (hp : Nat.Prime p) : sigma1 p = p + 1 := by
  rw [sigma1, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  exact Nat.add_comm 1 p

lemma geom_two_succ (k : ℕ) : (∑ x ∈ Finset.range (k + 1), 2 ^ x) + 1 = 2 ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [Nat.add_right_comm, ih]
      ring

lemma sigma1_two_pow (k : ℕ) : sigma1 (2 ^ k) + 1 = 2 ^ (k + 1) := by
  have h : sigma1 (2 ^ k) = ∑ x ∈ Finset.range (k + 1), 2 ^ x := by
    simpa [sigma1] using
      (Nat.sum_divisors_prime_pow (f := fun d => d) (k := k) Nat.prime_two)
  rw [h, geom_two_succ]

/-- The sum of divisors of `2 ^ k * p` for an odd prime `p`. -/
lemma sigma1_two_pow_mul_prime {k p : ℕ} (hp : Nat.Prime p) (hodd : Odd p) :
    sigma1 (2 ^ k * p) + (p + 1) = 2 ^ (k + 1) * (p + 1) := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    simp [Nat.odd_iff] at hodd
  have hcop : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have h : sigma1 (2 ^ k * p) = sigma1 (2 ^ k) * sigma1 p := hcop.sum_divisors_mul
  rw [h, sigma1_prime hp, ← sigma1_two_pow k]
  ring

/-- Sum of divisors of a product of two distinct primes. -/
lemma sigma1_mul_of_distinct_primes {q r : ℕ} (hq : Nat.Prime q) (hr : Nat.Prime r)
    (hne : q ≠ r) : sigma1 (q * r) = (q + 1) * (r + 1) := by
  have hcop : Nat.Coprime q r := (Nat.coprime_primes hq hr).mpr hne
  rw [show sigma1 (q * r) = sigma1 q * sigma1 r from hcop.sum_divisors_mul,
    sigma1_prime hq, sigma1_prime hr]

/-- Sum of divisors of the square of a prime. -/
lemma sigma1_prime_sq {q : ℕ} (hq : Nat.Prime q) : sigma1 (q * q) = 1 + q + q * q := by
  have h : sigma1 (q ^ 2) = ∑ x ∈ Finset.range 3, q ^ x := by
    simpa [sigma1] using
      (Nat.sum_divisors_prime_pow (f := fun d => d) (k := 2) hq)
  have h2 : q * q = q ^ 2 := (sq q).symm
  rw [h2, h]
  simp [Finset.sum_range_succ, sq]

/-- **Unique partner**: if `m` is betrothed to `2 ^ k * p` with `p` an odd prime,
then `m = (2 ^ k - 1) * (p + 2)`. -/
lemma unique_partner {k p m : ℕ} (hp : Nat.Prime p) (hodd : Odd p)
    (h : IsBetrothedPair (2 ^ k * p) m) : m = (2 ^ k - 1) * (p + 2) := by
  obtain ⟨h1, -⟩ := h
  have hs := sigma1_two_pow_mul_prime (k := k) hp hodd
  rw [h1] at hs
  have hq1 : 2 ^ k - 1 + 1 = 2 ^ k := Nat.succ_pred_eq_of_pos (Nat.two_pow_pos k)
  set q : ℕ := 2 ^ k - 1 with hqdef
  have hpow : (2 : ℕ) ^ (k + 1) = 2 * (q + 1) := by
    rw [pow_succ, hq1]; ring
  rw [hpow] at hs
  -- hs : 2 ^ k * p + m + 1 + (p + 1) = 2 * (q + 1) * (p + 1)
  rw [← hq1] at hs
  nlinarith [hs]

/-- **Target.** Let `k ≥ 2` and let `p` be an odd prime.  If `2 ^ k - 1` and `p + 2`
are both prime, then no `m` forms a betrothed pair with `2 ^ k * p`. -/
theorem no_pair_of_mersenne_and_shifted_prime {k p : ℕ} (hk : 2 ≤ k) (hp : Nat.Prime p)
    (hodd : Odd p) (hq : Nat.Prime (2 ^ k - 1)) (hr : Nat.Prime (p + 2)) (m : ℕ) :
    ¬ IsBetrothedPair (2 ^ k * p) m := by
  intro h
  have hm : m = (2 ^ k - 1) * (p + 2) := unique_partner hp hodd h
  have hq1 : 2 ^ k - 1 + 1 = 2 ^ k := Nat.succ_pred_eq_of_pos (Nat.two_pow_pos k)
  set q : ℕ := 2 ^ k - 1 with hqdef
  have hq3 : 3 ≤ q := by
    have : (4 : ℕ) ≤ 2 ^ k := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  have hp3 : 3 ≤ p := by
    have h2le := hp.two_le
    have := Nat.odd_iff.mp hodd
    omega
  obtain ⟨-, h2⟩ := h
  rw [hm, ← hq1] at h2
  by_cases hqr : q = p + 2
  · -- the two auxiliary primes coincide, so `m = q ^ 2`
    rw [← hqr] at h2
    rw [sigma1_prime_sq hq] at h2
    nlinarith [h2, hq3, hp3]
  · rw [sigma1_mul_of_distinct_primes hq hr hqr] at h2
    nlinarith [h2, hq3, hp3]

end Brockian.BetrothedNumbers

