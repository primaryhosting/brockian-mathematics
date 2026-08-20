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

def allOnes : Fin 8 → Bool := fun _ => true

/-- The 8-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2`, as a vector in the
`2^8`-dimensional complex Hilbert space `EuclideanSpace ℂ (Fin 8 → Bool)`. -/
