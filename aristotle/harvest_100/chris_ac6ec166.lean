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

/-- Two positive natural numbers `m ≠ n` are a *betrothed* (quasi-amicable) pair when the sum of
the divisors of each of them equals `m + n + 1`, i.e. each is the sum of the *proper* divisors
of the other, excluding `1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ σ 1 m = m + n + 1 ∧ σ 1 n = m + n + 1

/-- `σ₁` of a prime. -/
lemma sigma_one_of_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  have h := ArithmeticFunction.sigma_one_apply_prime_pow (p := p) (i := 1) hp
  simpa [Finset.sum_range_succ, add_comm] using h

/-- `σ₁` of a power of two. -/
lemma sigma_one_two_pow (k : ℕ) : σ 1 (2 ^ k) = 2 ^ (k + 1) - 1 := by
  have h := ArithmeticFunction.sigma_one_apply_prime_pow (p := 2) (i := k) Nat.prime_two
  rw [h, Nat.geomSum_eq (le_refl 2)]
  simp

/-- `σ₁` of the square of a prime. -/
lemma sigma_one_of_prime_sq {q : ℕ} (hq : q.Prime) : σ 1 (q ^ 2) = 1 + q + q ^ 2 := by
  have h := ArithmeticFunction.sigma_one_apply_prime_pow (p := q) (i := 2) hq
  rw [h]
  simp [Finset.sum_range_succ]

/-- `σ₁` of a product of two distinct primes. -/
lemma sigma_one_of_distinct_primes {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r) :
    σ 1 (q * r) = (q + 1) * (r + 1) := by
  have hcop : Nat.Coprime q r := (Nat.coprime_primes hq hr).mpr hqr
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
    sigma_one_of_prime hq, sigma_one_of_prime hr]

/-- `σ₁` of `2 ^ k * p` for an odd prime `p`. -/
lemma sigma_one_two_pow_mul_odd_prime {k p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    σ 1 (2 ^ k * p) = (2 ^ (k + 1) - 1) * (p + 1) := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    simp [Nat.odd_iff] at hodd
  have hcop : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_two_pow,
    sigma_one_of_prime hp]

/-- **Unique partner.** If `m` forms a betrothed pair with `2 ^ k * p` (`p` an odd prime), then
necessarily `m = (2 ^ k - 1) * (p + 2)`. -/
theorem betrothed_partner_eq {k p m : ℕ} (hp : p.Prime) (hodd : Odd p)
    (h : IsBetrothedPair (2 ^ k * p) m) : m = (2 ^ k - 1) * (p + 2) := by
  obtain ⟨-, -, -, hσn, -⟩ := h
  rw [sigma_one_two_pow_mul_odd_prime hp hodd] at hσn
  have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  obtain ⟨q, hq⟩ : ∃ q, 2 ^ k = q + 1 := ⟨2 ^ k - 1, by omega⟩
  have hpow : 2 ^ (k + 1) = 2 * (q + 1) := by rw [pow_succ, hq]; ring
  rw [hpow, hq] at hσn
  have hq1 : 2 * (q + 1) - 1 = 2 * q + 1 := by omega
  rw [hq1] at hσn
  have hmq : m = q * (p + 2) := by nlinarith [hσn]
  rw [hmq, hq]
  simp

/-- **Target.** For `k ≥ 2` and an odd prime `p` such that both `2 ^ k - 1` and `p + 2` are prime,
no natural number forms a betrothed pair with `2 ^ k * p`. -/
theorem no_pair_of_mersenne_and_shifted_prime {k p : ℕ} (hk : 2 ≤ k) (hp : p.Prime) (hodd : Odd p)
    (hq : Nat.Prime (2 ^ k - 1)) (hr : Nat.Prime (p + 2)) :
    ¬ ∃ m : ℕ, IsBetrothedPair (2 ^ k * p) m := by
  rintro ⟨m, hm⟩
  have hmeq : m = (2 ^ k - 1) * (p + 2) := betrothed_partner_eq hp hodd hm
  obtain ⟨-, -, -, hσn, hσm⟩ := hm
  rw [sigma_one_two_pow_mul_odd_prime hp hodd] at hσn
  -- basic numeric facts
  have hk4 : 4 ≤ 2 ^ k := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  set Q : ℕ := 2 ^ k - 1 with hQdef
  have hQ : 2 ^ k = Q + 1 := by omega
  have hQ3 : 3 ≤ Q := by omega
  have hpow : 2 ^ (k + 1) = 2 * (Q + 1) := by rw [pow_succ, hQ]; ring
  have hp3 : 3 ≤ p := by
    have hp2 : p ≠ 2 := by
      rintro rfl
      simp [Nat.odd_iff] at hodd
    have := hp.two_le
    omega
  rw [hpow] at hσn
  have hQ1 : 2 * (Q + 1) - 1 = 2 * Q + 1 := by omega
  rw [hQ1, hQ] at hσn
  -- σ(m) = σ(n) = n + m + 1
  have hσmn : σ 1 m = (2 * Q + 1) * (p + 1) := by rw [hσm, hσn, hQ]
  rw [hmeq] at hσmn
  by_cases hcase : Q = p + 2
  · -- the two auxiliary primes coincide: m = Q ^ 2
    have hsq : Q * (p + 2) = Q ^ 2 := by rw [← hcase]; ring
    rw [hsq, sigma_one_of_prime_sq hq] at hσmn
    rw [hcase] at hσmn
    nlinarith [hσmn, hp3]
  · rw [sigma_one_of_distinct_primes hq hr hcase] at hσmn
    nlinarith [hσmn]

/-- Sanity check that the definition is the intended one: `(48, 75)`, the smallest betrothed
pair, satisfies `IsBetrothedPair`. -/
example : IsBetrothedPair 48 75 :=
  ⟨by norm_num, by norm_num, by norm_num, by decide, by decide⟩

/-- Sanity check that the hypotheses of the target theorem are satisfiable: `k = 2`, `p = 3`,
with `2 ^ 2 - 1 = 3` and `3 + 2 = 5` both prime. -/
example : ¬ ∃ m : ℕ, IsBetrothedPair (2 ^ 2 * 3) m :=
  no_pair_of_mersenne_and_shifted_prime (le_refl 2) (by norm_num) (by decide) (by norm_num)
    (by norm_num)

#print axioms Brockian.BetrothedNumbers.no_pair_of_mersenne_and_shifted_prime

end Brockian.BetrothedNumbers

