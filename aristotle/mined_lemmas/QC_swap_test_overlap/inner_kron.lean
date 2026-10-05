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

open scoped ComplexConjugate

/-- The tensor (Kronecker) product of two `n`-dimensional pure states, viewed as a vector
indexed by pairs: `(x ⊗ y) (i, j) = x i * y j`. -/

theorem inner_kron {n : ℕ} (a b c d : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (kron a b) (kron c d) = inner ℂ a c * inner ℂ b d := by
  simp only [kron, PiLp.inner_apply, RCLike.inner_apply, Fintype.sum_prod_type,
    map_mul, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The acceptance probability of the SWAP test on the input states `x` and `y`.

In the SWAP test the control qubit is measured after a Hadamard–controlled-SWAP–Hadamard
circuit; the outcome `0` ("accept") occurs with probability equal to the squared norm of the
component `½ (x ⊗ y + y ⊗ x)` of the state on the two registers. -/
