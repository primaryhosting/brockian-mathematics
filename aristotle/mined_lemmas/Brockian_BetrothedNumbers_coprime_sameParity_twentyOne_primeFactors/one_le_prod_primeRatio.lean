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

lemma one_le_prod_primeRatio {S : Finset ℕ} (h : ∀ p ∈ S, 1 ≤ primeRatio p) :
    1 ≤ ∏ p ∈ S, primeRatio p := by
  calc (1 : ℚ) = ∏ _p ∈ S, (1 : ℚ) := by simp
    _ ≤ ∏ p ∈ S, primeRatio p :=
        Finset.prod_le_prod (fun _ _ => zero_le_one) (fun p hp => h p hp)

