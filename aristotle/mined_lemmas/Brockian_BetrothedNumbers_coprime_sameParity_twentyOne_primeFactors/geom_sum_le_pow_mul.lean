import Mathlib

/-!
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 4000000
set_option maxRecDepth 40000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-! ## The definition -/

/-- A *betrothed* (quasi-amicable) pair: two positive integers each of whose sum of
divisors equals the sum of the two numbers plus one, i.e. `σ₁(m) = σ₁(n) = m + n + 1`. -/

lemma geom_sum_le_pow_mul {p : ℕ} (hp : 2 ≤ p) (e : ℕ) :
    (∑ i ∈ Finset.range (e + 1), (p : ℚ) ^ i) ≤ (p : ℚ) ^ e * ((p : ℚ) / ((p : ℚ) - 1)) := by
  have hx : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
  have h1 : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  rw [mul_div_assoc', le_div_iff₀ h1, geom_sum_mul]
  have hpos : (0 : ℚ) < (p : ℚ) ^ (e + 1) := by positivity
  rw [pow_succ] at *
  linarith

/-- `σ₁(n) ≤ n · ∏_{p ∣ n} p/(p-1)`. -/
