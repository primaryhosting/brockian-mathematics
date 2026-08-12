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

namespace Brockian
namespace BetrothedNumbers

/-- Sum-of-divisors function `σ₁`. -/
local notation "σ₁" => ArithmeticFunction.sigma 1

/-- Two positive naturals `n ≠ m` form a *betrothed* (quasi-amicable) pair when the sum of the
divisors of each of them equals `n + m + 1`. -/
def IsBetrothedPair (n m : ℕ) : Prop :=
  0 < n ∧ 0 < m ∧ n ≠ m ∧ σ₁ n = n + m + 1 ∧ σ₁ m = n + m + 1

/-- `σ₁` of a prime. -/
lemma sigma_one_prime {p : ℕ} (hp : p.Prime) : σ₁ p = p + 1 := by
  rw [sigma_one_apply, hp.sum_divisors]

/-- `σ₁` of the square of a prime. -/
lemma sigma_one_prime_sq {p : ℕ} (hp : p.Prime) : σ₁ (p ^ 2) = 1 + p + p ^ 2 := by
  rw [sigma_one_apply, Nat.sum_divisors_prime_pow hp]
  simp [Finset.sum_range_succ]

/-- `σ₁` of a power of two, stated without natural subtraction. -/
lemma sigma_one_two_pow (k : ℕ) : σ₁ (2 ^ k) + 1 = 2 ^ (k + 1) := by
  rw [sigma_one_apply, Nat.sum_divisors_prime_pow Nat.prime_two]
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have h2 : (2 : ℕ) ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by ring
      omega

/-- `σ₁` of a product of two distinct primes. -/
lemma sigma_one_mul_distinct_primes {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hne : q ≠ r) :
    σ₁ (q * r) = (q + 1) * (r + 1) := by
  have hcop : Nat.Coprime q r := (Nat.coprime_primes hq hr).mpr hne
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_prime hq, sigma_one_prime hr]

/-- `σ₁ (2 ^ k * p)` for `p` an odd prime. -/
lemma sigma_one_two_pow_mul_odd_prime {k p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    σ₁ (2 ^ k * p) = (σ₁ (2 ^ k)) * (p + 1) := by
  have hcop : Nat.Coprime (2 ^ k) p := (Nat.coprime_two_left.mpr hodd).pow_left k
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_prime hp]

/-- **Unique partner.** If `σ₁ (2 ^ k * p) = 2 ^ k * p + m + 1` for an odd prime `p`, then
`m = (2 ^ k - 1) * (p + 2)`. -/
theorem partner_unique {k p m : ℕ} (hp : p.Prime) (hodd : Odd p)
    (h : σ₁ (2 ^ k * p) = 2 ^ k * p + m + 1) : m = (2 ^ k - 1) * (p + 2) := by
  obtain ⟨T, hT⟩ : ∃ T : ℕ, 2 ^ k = T + 1 := ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
  have hSval : σ₁ (2 ^ k) = 2 * T + 1 := by
    have h1 := sigma_one_two_pow k
    have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    omega
  have h' : (2 * T + 1) * (p + 1) = (T + 1) * p + m + 1 := by
    rw [← hSval, ← sigma_one_two_pow_mul_odd_prime hp hodd, h, hT]
  have hexp : (2 * T + 1) * (p + 1) = 2 * (T * p) + 2 * T + p + 1 := by ring
  have hexp2 : (T + 1) * p = T * p + p := by ring
  have hgoal : m = T * p + 2 * T := by omega
  have hfin : T * (p + 2) = T * p + 2 * T := by ring
  rw [hT]
  simpa using hgoal.trans hfin.symm

/-- Arithmetic contradiction in the case where the two auxiliary primes `2 ^ k - 1` and `p + 2`
are distinct. -/
lemma no_solution_distinct {q p m : ℕ} (hq3 : 3 ≤ q) (hp3 : 3 ≤ p) (hm : m = q * (p + 2))
    (h : (q + 1) * (p + 3) = (q + 1) * p + m + 1) : False := by
  subst hm
  nlinarith [h, hq3, hp3]

/-- Arithmetic contradiction in the case where the two auxiliary primes `2 ^ k - 1` and `p + 2`
coincide. -/
lemma no_solution_equal {q p m : ℕ} (hq3 : 3 ≤ q) (hpq : p + 2 = q) (hm : m = q ^ 2)
    (h : 1 + q + q ^ 2 = (q + 1) * p + m + 1) : False := by
  subst hm
  nlinarith [h, hq3, hpq]

/-- **Target.** Let `k ≥ 2` and let `p` be an odd prime.  If both `2 ^ k - 1` and `p + 2` are
prime, then no `m` forms a betrothed pair with `2 ^ k * p`. -/
theorem no_pair_of_mersenne_and_shifted_prime {k p : ℕ} (hk : 2 ≤ k) (hp : p.Prime) (hodd : Odd p)
    (hqp : Nat.Prime (2 ^ k - 1)) (hrp : Nat.Prime (p + 2)) :
    ∀ m : ℕ, ¬ IsBetrothedPair (2 ^ k * p) m := by
  rintro m ⟨-, -, -, hn, hm⟩
  have hT4 : 4 ≤ 2 ^ k := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  obtain ⟨q, hqT⟩ : ∃ q : ℕ, 2 ^ k = q + 1 := ⟨2 ^ k - 1, by omega⟩
  have hq3 : 3 ≤ q := by omega
  have hq : Nat.Prime q := by
    have hqe : 2 ^ k - 1 = q := by omega
    rwa [hqe] at hqp
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    rcases Nat.lt_or_ge p 3 with hlt | hge
    · interval_cases p
      · exact absurd hodd (by decide)
    · exact hge
  -- the partner is forced
  have hmval : m = q * (p + 2) := by
    have := partner_unique hp hodd hn
    rw [this]
    congr 1
    omega
  -- rewrite the defining equation for `m`
  have hmeq : σ₁ m = (q + 1) * p + m + 1 := by rw [hm, hqT]
  by_cases hcase : q = p + 2
  · have hm2 : m = q ^ 2 := by rw [hmval, ← hcase]; ring
    have hsq : σ₁ m = 1 + q + q ^ 2 := by rw [hm2]; exact sigma_one_prime_sq hq
    exact no_solution_equal hq3 hcase.symm hm2 (by rw [← hsq]; exact hmeq)
  · have hsig2 : σ₁ m = (q + 1) * (p + 3) := by
      rw [hmval, sigma_one_mul_distinct_primes hq hrp hcase]
    exact no_solution_distinct hq3 hp3 hmval (by rw [← hsig2]; exact hmeq)

end BetrothedNumbers
end Brockian

