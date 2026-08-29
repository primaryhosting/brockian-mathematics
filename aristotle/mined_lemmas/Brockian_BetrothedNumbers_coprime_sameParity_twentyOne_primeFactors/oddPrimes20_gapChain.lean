/-
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

namespace Brockian
namespace BetrothedNumbers

open Finset

/-! ## Basic definitions -/

/-- `sigmaOne n` is the sum-of-divisors function `σ₁(n) = ∑_{d ∣ n} d`. -/

lemma oddPrimes20_gapChain :
    oddPrimes20.IsChain (fun a b => ∀ p : ℕ, p.Prime → a < p → b ≤ p) := by
  simp only [oddPrimes20, List.isChain_cons_cons, List.isChain_singleton, and_true]
  and_intros <;>
    (intro p hp h; by_contra hc; push_neg at hc; interval_cases p <;> revert hp <;> decide)

