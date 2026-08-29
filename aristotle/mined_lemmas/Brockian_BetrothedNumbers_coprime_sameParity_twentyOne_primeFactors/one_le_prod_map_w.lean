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

lemma one_le_prod_map_w :
    ∀ (L : List ℕ), (∀ b ∈ L, 2 ≤ b) → 1 ≤ (L.map w).prod := by
  intro L
  induction L with
  | nil => simp
  | cons b T ih =>
      intro h
      simp only [List.map_cons, List.prod_cons]
      have h1 := one_le_w (h b (by simp))
      have h2 := ih fun x hx => h x (by simp [hx])
      nlinarith

/-- Greedy comparison: if every element of `S` is a prime bounded below by the head of a
"gap chain" list `L`, and `S` has at most `L.length` elements, then `∏_{p ∈ S} w p` is at most
the product of `w` over `L`. -/
