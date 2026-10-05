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

def ones8 : Qubits8 := fun _ => 1

