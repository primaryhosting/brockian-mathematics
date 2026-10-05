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

noncomputable def swapTestState (psi phi : n → ℂ) : Bool × n × n → ℂ :=
  hadamardAncilla (cswap (hadamardAncilla (initState psi phi)))

/-- The SWAP test *accepts* when the ancilla is measured in `|0⟩`; this is the
corresponding probability. -/
