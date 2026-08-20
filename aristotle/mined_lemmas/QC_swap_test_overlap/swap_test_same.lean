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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Finset Complex

variable {n : ℕ}

/-- The inner product `⟨ψ|φ⟩` of two (finite dimensional) state vectors,
antilinear in the first argument. -/

theorem swap_test_same (ψ : Fin n → ℂ) (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) :
    acceptProb ψ ψ = 1 := by
  have hb : braket ψ ψ = 1 := by
    have h : braket ψ ψ = ((∑ i, ‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
      rw [braket, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ofReal_norm_sq, mul_comm]
    rw [h, hψ, Complex.ofReal_one]
  rw [swap_test_overlap ψ ψ hψ hψ, hb]
  norm_num

/-- Sanity check: on orthogonal states the swap test accepts with probability `1/2`. -/
