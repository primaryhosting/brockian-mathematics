/-
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
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

namespace Phys

open Finset

/-- Shannon entropy (in nats) of a finite probability distribution `p`. -/

theorem landauer_bound_of_entropy_balance {α : Type*} [Fintype α] (p q : α → ℝ)
    (k T Q σ : ℝ) (hk : 0 < k) (hT : 0 < T) (hσ : 0 ≤ σ)
    (hbalance : σ = (shannonEntropy q - shannonEntropy p) + Q / (k * T)) :
    k * T * (shannonEntropy p - shannonEntropy q) ≤ Q := by
  have hkT : 0 < k * T := mul_pos hk hT
  have h : shannonEntropy p - shannonEntropy q ≤ Q / (k * T) := by linarith
  calc k * T * (shannonEntropy p - shannonEntropy q) ≤ k * T * (Q / (k * T)) :=
        mul_le_mul_of_nonneg_left h (le_of_lt hkT)
    _ = Q := by field_simp

/-- **Landauer's principle.**  Erasing one bit of information — resetting a memory that is
uniformly distributed over its two states to the definite state `false` — while in contact with
a heat bath at absolute temperature `T > 0` dissipates at least `k T log 2` of heat.

The only physical input is the second law of thermodynamics, in the form that the total entropy
production `σ = ΔS_memory + Q / (k T)` of the process is nonnegative; the bound
`Q ≥ k T log 2` is then derived, the value `log 2` being the exact entropy content of one bit. -/
