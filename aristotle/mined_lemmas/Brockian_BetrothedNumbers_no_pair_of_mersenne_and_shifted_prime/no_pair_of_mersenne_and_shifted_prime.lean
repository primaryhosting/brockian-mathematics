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

