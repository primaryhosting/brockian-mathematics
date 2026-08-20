import Mathlib

/-!
# Ghz 6 Normalized
Category: Quantum Computing
Target: QC.ghz6_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The computational basis of a 6-qubit register: bit strings of length 6. -/
abbrev Bits6 := Fin 6 → Bool

/-- The all-zeros bit string, labelling the basis vector `|000000⟩`. -/

def allOne : Bits6 := fun _ => true

