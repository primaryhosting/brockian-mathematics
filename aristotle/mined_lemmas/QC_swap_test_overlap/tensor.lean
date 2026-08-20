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

noncomputable def tensor (ψ φ : EuclideanSpace ℂ (Fin n)) : Fin n × Fin n → ℂ :=
  fun p => ψ p.1 * φ p.2

/-- A state of the whole swap-test register: one ancilla qubit (`Fin 2`) together
with the two `n`-level registers. -/
abbrev State (n : ℕ) := Fin 2 × (Fin n × Fin n) → ℂ

/-- The Hadamard gate acting on the ancilla qubit:
`|0⟩ ↦ (|0⟩+|1⟩)/√2`, `|1⟩ ↦ (|0⟩-|1⟩)/√2`. -/
