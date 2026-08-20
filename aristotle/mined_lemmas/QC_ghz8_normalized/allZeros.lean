/-
# Ghz 8 Normalized
Category: Quantum Computing
Target: QC.ghz8_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open EuclideanSpace

/-- The all-zeros basis state index `|00000000⟩` of an 8-qubit register,
represented as the constant `false` function on `Fin 8`. -/

def allZeros : Fin 8 → Bool := fun _ => false

/-- The all-ones basis state index `|11111111⟩` of an 8-qubit register,
represented as the constant `true` function on `Fin 8`. -/
