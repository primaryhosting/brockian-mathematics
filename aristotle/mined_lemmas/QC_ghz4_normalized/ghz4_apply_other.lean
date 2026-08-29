/-
# Ghz 4 Normalized
Category: Quantum Computing
Target: QC.ghz4_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ghz 4 Normalized
Category: Quantum Computing
Target: QC.ghz4_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The all-zeros computational basis label `|0000⟩` for four qubits. -/

lemma ghz4_apply_other {x : Fin 4 → Fin 2} (h0 : x ≠ allZeros) (h1 : x ≠ allOnes) :
    ghz4.ofLp x = 0 := by
  simp [ghz4, h0, h1]

