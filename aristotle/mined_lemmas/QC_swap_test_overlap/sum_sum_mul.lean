/-
/-!
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

namespace QC

open Finset

variable {n : ℕ}

/-- The Hermitian inner product `⟨ψ|φ⟩ = ∑ i, conj (ψ i) * φ i` of two vectors of `ℂ^n`. -/

private lemma sum_sum_mul (f g : Fin n → ℂ) :
    ∑ i, ∑ j, f i * g j = (∑ i, f i) * (∑ j, g j) := by
  rw [Finset.sum_mul_sum]

