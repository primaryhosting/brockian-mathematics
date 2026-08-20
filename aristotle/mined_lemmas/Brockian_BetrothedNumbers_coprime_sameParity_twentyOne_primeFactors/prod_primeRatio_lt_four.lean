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

lemma prod_primeRatio_lt_four {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p ∧ p ≠ 2)
    (hc : S.card ≤ 20) : ∏ p ∈ S, primeRatio p < 4 := by
  have h := prod_primeRatio_le_prod_oddPrimesBelow 20 le_rfl S hS hc
  have hb : bnd 20 = 79 := by decide
  rw [hb] at h
  exact lt_of_le_of_lt h prod_oddPrimesBelow_79_lt_four

/-! ## The main theorem -/

/-- **Hagis–Lord, Proposition 2 (second part).**  If `(m, n)` is a coprime betrothed pair
whose members have the same parity, then both members are odd and the product `m * n`
has at least twenty-one distinct prime factors. -/
