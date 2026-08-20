/-
# Ghz 5 Normalized
Category: Quantum Computing
Target: QC.ghz5_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- Computational basis states of a 5-qubit register are indexed by `Fin 5 → Bool`. -/
abbrev Qubits5 := Fin 5 → Bool

/-- The all-zeros bit string `|00000⟩`. -/

theorem ghz5_apply (x : Qubits5) :
    ghz5.ofLp x =
      if x = allZeros then ((1 / Real.sqrt 2 : ℝ) : ℂ)
      else if x = allOnes then ((1 / Real.sqrt 2 : ℝ) : ℂ)
      else 0 := rfl

