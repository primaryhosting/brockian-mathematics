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

theorem landauer_principle_of_initial_state (p : Bool → ℝ) (h0 : ∀ b, 0 ≤ p b)
    (hsum : p false + p true = 1) (k T Q σ : ℝ) (hk : 0 < k) (hT : 0 < T) (hσ : 0 ≤ σ)
    (hbalance : σ = (shannonEntropy erasedBit - shannonEntropy p) + Q / (k * T)) :
    k * T * shannonEntropy p ≤ Q ∧ k * T * shannonEntropy p ≤ k * T * Real.log 2 := by
  have h := landauer_bound_of_entropy_balance p erasedBit k T Q σ hk hT hσ hbalance
  rw [shannonEntropy_erasedBit, sub_zero] at h
  refine ⟨h, ?_⟩
  exact mul_le_mul_of_nonneg_left (shannonEntropy_bool_le_log_two p h0 hsum)
    (le_of_lt (mul_pos hk hT))

/-- The Landauer bound is sharp: a reversible erasure (zero entropy production) releases
exactly `k T log 2` of heat, so no larger lower bound is possible. -/
