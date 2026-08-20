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

lemma swapTestFinal_zero (ψ φ : Fin n → ℂ) (i j : Fin n) :
    swapTestFinal ψ φ (0, i, j) = (1 / 2 : ℂ) * (ψ i * φ j + ψ j * φ i) := by
  simp only [swapTestFinal, hadamardAncilla, cswap, inputState]
  norm_num
  ring_nf
  rw [show (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ 2 = 1 / 2 by rw [sq]; exact sqrt_two_inv_sq]
  ring

/-- **Swap test.**  For two normalised states `ψ` and `φ`, the swap test accepts
with probability `(1 + |⟨ψ|φ⟩|²)/2`. -/
