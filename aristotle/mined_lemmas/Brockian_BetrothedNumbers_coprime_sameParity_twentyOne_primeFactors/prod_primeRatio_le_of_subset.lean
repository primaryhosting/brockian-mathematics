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

lemma prod_primeRatio_le_of_subset {S T : Finset ℕ} (hst : S ⊆ T)
    (h1 : ∀ p ∈ T, 1 ≤ primeRatio p) :
    ∏ p ∈ S, primeRatio p ≤ ∏ p ∈ T, primeRatio p := by
  rw [← Finset.prod_sdiff hst]
  have hA : 1 ≤ ∏ p ∈ T \ S, primeRatio p :=
    one_le_prod_primeRatio (fun p hp => h1 p (Finset.mem_sdiff.mp hp).1)
  have hB : 0 ≤ ∏ p ∈ S, primeRatio p :=
    le_trans zero_le_one (one_le_prod_primeRatio (fun p hp => h1 p (hst hp)))
  nlinarith

/-- Greedy comparison: a set of at most `k` odd primes has `∏ p/(p-1)` at most the
corresponding product over the `k` smallest odd primes. -/
