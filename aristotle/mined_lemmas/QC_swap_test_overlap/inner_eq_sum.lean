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

open scoped ComplexConjugate

namespace QC

variable {n : ℕ}

/-- The product state `ψ ⊗ φ` of two `n`-level registers, as a vector indexed by
pairs of basis labels. -/

lemma inner_eq_sum (ψ φ : EuclideanSpace ℂ (Fin n)) :
    (inner ℂ ψ φ : ℂ) = ∑ i, conj (ψ i) * φ i := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- The key computation: for unit vectors `ψ`, `φ` and any coefficient `c`, the
squared norm of the (unnormalized) branch `ψ ⊗ φ + c • (φ ⊗ ψ)`. -/
