/-
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open ComplexConjugate

namespace QC

variable {n : Type*} [Fintype n]

/-- The overlap `⟨ψ|φ⟩` of two state vectors indexed by `n`. -/

def IsNormalized (psi : n → ℂ) : Prop := ∑ i, ‖psi i‖ ^ 2 = 1

/-- The initial state of the SWAP-test circuit: an ancilla qubit in `|0⟩`
(indexed by `false`) together with the two registers in state `|ψ⟩ ⊗ |φ⟩`. -/
