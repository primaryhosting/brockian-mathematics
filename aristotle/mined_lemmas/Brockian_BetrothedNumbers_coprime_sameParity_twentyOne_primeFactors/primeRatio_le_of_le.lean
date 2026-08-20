import Mathlib

/-!
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
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

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-- `Betrothed m n` says that `(m, n)` is a betrothed (quasi-amicable) pair:
both are positive and `σ m = σ n = m + n + 1`. -/

lemma primeRatio_le_of_le {p q : ℕ} (hq : 2 ≤ q) (hqp : q ≤ p) :
    primeRatio p ≤ primeRatio q := by
  have hq' : (2 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hqp' : (q : ℚ) ≤ (p : ℚ) := by exact_mod_cast hqp
  rw [primeRatio, primeRatio, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- The local bound `σ (p ^ a) ≤ p ^ a * (p / (p - 1))`. -/
