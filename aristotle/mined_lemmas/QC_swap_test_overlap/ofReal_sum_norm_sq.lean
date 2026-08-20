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

private lemma ofReal_sum_norm_sq (g : Fin n × Fin n → ℂ) :
    ((∑ x : Fin n × Fin n, ‖g x‖ ^ 2 : ℝ) : ℂ) = ∑ x : Fin n × Fin n, g x * conj (g x) := by
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [Complex.mul_conj']; push_cast; ring

/-- **Swap test.** For two unit vectors `ψ` and `φ`, the swap test
(Hadamard, controlled-SWAP, Hadamard, then measure the ancilla) accepts with
probability `(1 + |⟨ψ, φ⟩|²)/2`. -/
