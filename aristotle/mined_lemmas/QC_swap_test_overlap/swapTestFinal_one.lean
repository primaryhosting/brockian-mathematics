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

lemma swapTestFinal_one (ψ φ : EuclideanSpace ℂ (Fin n)) (x : Fin n × Fin n) :
    swapTestFinal ψ φ (1, x) = (ψ x.1 * φ x.2 + (-1) * (φ x.1 * ψ x.2)) / 2 := by
  have hne := sqrt_two_ne_zero
  simp only [swapTestFinal, hadamardAncilla, cswap, initState, tensor]
  norm_num [Prod.swap]
  field_simp
  rw [sqrt_two_sq]
  ring

end Amplitudes

/-- For a unit vector the amplitudes have squared moduli summing to one. -/
