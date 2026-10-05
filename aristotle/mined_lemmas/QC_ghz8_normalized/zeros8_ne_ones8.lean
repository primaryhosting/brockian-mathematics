/-
# Ghz 8 Normalized
Category: Quantum Computing
Target: QC.ghz8_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ghz 8 Normalized
Category: Quantum Computing
Target: QC.ghz8_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

namespace QC

/-- Computational basis states of 8 qubits, indexed by bit strings `Fin 8 → Fin 2`. -/
abbrev Qubits8 := Fin 8 → Fin 2

/-- The all-zeros bit string `|0…0⟩`. -/

theorem zeros8_ne_ones8 : zeros8 ≠ ones8 := by
  intro h
  have := congrFun h ⟨0, by norm_num⟩
  simp [zeros8, ones8] at this

/-- The 8-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2`, as a vector in the
256-dimensional complex Hilbert space `EuclideanSpace ℂ (Fin 8 → Fin 2)`. -/
