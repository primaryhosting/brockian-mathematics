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

theorem swap_test_orthogonal (ψ φ : Fin n → ℂ)
    (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) (hφ : ∑ i, ‖φ i‖ ^ 2 = 1) (h : braket ψ φ = 0) :
    acceptProb ψ φ = 1 / 2 := by
  rw [swap_test_overlap ψ φ hψ hφ, h]
  norm_num

end QC

