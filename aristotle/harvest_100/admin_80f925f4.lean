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

namespace Brockian.BetrothedNumbers

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- The sum-of-divisors function `σ₁`. -/
def sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

lemma sigmaOne_eq_sigma (n : ℕ) : sigmaOne n = σ 1 n := (sigma_one_apply n).symm

/-- `m` and `n` form a betrothed (quasi-amicable) pair:
each is the sum of the *nontrivial* proper divisors of the other, i.e.
`σ₁ m = σ₁ n = m + n + 1`.  (Distinctness of `m` and `n` is not assumed, which
only makes the nonexistence statement below stronger.) -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ sigmaOne m = m + n + 1 ∧ sigmaOne n = m + n + 1

lemma sigmaOne_mul_of_coprime {a b : ℕ} (h : Nat.Coprime a b) :
    sigmaOne (a * b) = sigmaOne a * sigmaOne b :=
  Nat.Coprime.sum_divisors_mul h

lemma sigmaOne_prime {q : ℕ} (hq : q.Prime) : sigmaOne q = q + 1 := by
  simp [sigmaOne, hq.divisors, Finset.sum_pair hq.one_lt.ne, Nat.add_comm]

lemma sigmaOne_prime_sq {q : ℕ} (hq : q.Prime) : sigmaOne (q ^ 2) = 1 + q + q ^ 2 := by
  rw [sigmaOne_eq_sigma, sigma_one_apply_prime_pow hq]
  simp [Finset.sum_range_succ, sq]

lemma sum_range_two_pow (k : ℕ) : (∑ i ∈ Finset.range k, 2 ^ i) + 1 = 2 ^ k := by
  induction k with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, pow_succ]; omega

lemma sigmaOne_two_pow (k : ℕ) : sigmaOne (2 ^ k) + 1 = 2 ^ (k + 1) := by
  rw [sigmaOne_eq_sigma, sigma_one_apply_prime_pow Nat.prime_two]
  exact sum_range_two_pow (k + 1)

/-- For an odd prime `p`, `σ₁ (2^k p) = (2^{k+1} - 1)(p+1)`, stated without subtraction. -/
lemma sigmaOne_two_pow_mul_odd_prime {k p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    sigmaOne (2 ^ k * p) + (p + 1) = 2 ^ (k + 1) * (p + 1) := by
  have hcop : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  have h := sigmaOne_two_pow k
  rw [sigmaOne_mul_of_coprime hcop, sigmaOne_prime hp]
  nlinarith [h]

/-- Unique-partner theorem: if `m` is betrothed to `2^k p` with `p` an odd prime,
then `m = (2^k - 1)(p + 2)`.  (No lower bound on `k` is needed.) -/
theorem betrothed_partner_eq {k p m : ℕ} (hp : p.Prime) (hodd : Odd p)
    (h : IsBetrothedPair m (2 ^ k * p)) : m = (2 ^ k - 1) * (p + 2) := by
  obtain ⟨_, _, _, hn⟩ := h
  have hs : ∃ s : ℕ, 2 ^ k = s + 1 := ⟨2 ^ k - 1, by have : 0 < 2 ^ k := Nat.two_pow_pos k; omega⟩
  obtain ⟨s, hsk⟩ := hs
  have key := sigmaOne_two_pow_mul_odd_prime (k := k) hp hodd
  rw [hn, hsk] at key
  have h2 : (2 : ℕ) ^ (k + 1) = 2 * (s + 1) := by rw [pow_succ, hsk]; ring
  rw [h2] at key
  have : m = s * (p + 2) := by nlinarith [key]
  rw [this, hsk]
  simp

/-- **Negative obstruction.**  Let `k ≥ 2` and let `p` be an odd prime such that both
`2^k - 1` and `p + 2` are prime.  Then `2^k * p` has no betrothed partner. -/
theorem no_pair_of_mersenne_and_shifted_prime {k p : ℕ} (hk : 2 ≤ k) (hp : p.Prime)
    (hodd : Odd p) (hq : Nat.Prime (2 ^ k - 1)) (hr : Nat.Prime (p + 2)) :
    ¬ ∃ m : ℕ, IsBetrothedPair m (2 ^ k * p) := by
  rintro ⟨m, hm⟩
  have hmeq : m = (2 ^ k - 1) * (p + 2) := betrothed_partner_eq hp hodd hm
  obtain ⟨_, _, hsm, _⟩ := hm
  set q : ℕ := 2 ^ k - 1 with hqdef
  set r : ℕ := p + 2 with hrdef
  -- `2 ^ k = q + 1` and `q ≥ 3`
  have h1 : 4 ≤ 2 ^ k := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hpow : 2 ^ k = q + 1 := by omega
  have hq3 : 3 ≤ q := by omega
  have hp3 : 3 ≤ p := by
    obtain ⟨j, hj⟩ := hodd
    have := hp.two_le
    omega
  rw [hmeq] at hsm
  by_cases hqr : q = r
  · -- `m = q ^ 2`
    have hsq : q * r = q ^ 2 := by rw [← hqr]; ring
    rw [hsq, sigmaOne_prime_sq hq] at hsm
    -- forces `q = 2 ^ k * p`, impossible since `q < 2 ^ k ≤ 2 ^ k * p`
    have : q = 2 ^ k * p := by omega
    rw [hpow] at this
    nlinarith
  · have hcop : Nat.Coprime q r := (Nat.coprime_primes hq hr).mpr hqr
    rw [sigmaOne_mul_of_coprime hcop, sigmaOne_prime hq, sigmaOne_prime hr] at hsm
    rw [hpow] at hsm
    -- `(q+1)(p+3) = q(p+2) + (q+1)p + 1` forces `q * p = q + 2`, impossible
    have hkey : q * p = q + 2 := by nlinarith [hsm]
    nlinarith

end Brockian.BetrothedNumbers

