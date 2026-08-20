/-
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
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

open ArithmeticFunction

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: they are distinct positive
integers with `σ m = σ n = m + n + 1`. -/

lemma sigma_primePow_mul_pred_le {p : ℕ} (hp : p.Prime) (a : ℕ) :
    sigma 1 (p ^ a) * (p - 1) ≤ p ^ a * p := by
  have h2 := hp.two_le
  have hgeom : ∀ b : ℕ, (∑ i ∈ Finset.range (b + 1), p ^ i) * (p - 1) ≤ p ^ b * p := by
    intro b
    induction b with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, add_mul]
        have key : p ^ (k + 1) * (p - 1) + p ^ (k + 1) = p ^ (k + 1) * p := by
          obtain ⟨c, rfl⟩ : ∃ c, p = c + 1 := ⟨p - 1, by omega⟩
          simp; ring
        have hpk : p ^ k * p = p ^ (k + 1) := (pow_succ _ k).symm
        omega
  have hs : sigma 1 (p ^ a) = ∑ i ∈ Finset.range (a + 1), p ^ i := by
    rw [sigma_one_apply, Nat.sum_divisors_prime_pow hp]
  rw [hs]
  exact hgeom a

/-- Multiplying the prime-power estimates together over the factorization of `N`:
`σ(N) * ∏_{p ∣ N} (p - 1) ≤ N * ∏_{p ∣ N} p`, i.e. `σ(N)/N ≤ ∏_{p ∣ N} p/(p-1)`. -/
