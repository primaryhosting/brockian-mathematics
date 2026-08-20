/-
# Ghz 4 Normalized
Category: Quantum Computing
Target: QC.ghz4_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The state space of 4 qubits: the 16-dimensional complex Hilbert space whose
computational basis is indexed by bit strings `Fin 4 → Fin 2`. -/
abbrev Qubits4 : Type := EuclideanSpace ℂ (Fin 4 → Fin 2)

/-- The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2`. -/

noncomputable def ghz4 : Qubits4 :=
  (1 / Real.sqrt 2 : ℝ) •
    (EuclideanSpace.single (fun _ => 0) 1 + EuclideanSpace.single (fun _ => 1) 1)

/-- The amplitudes of `ghz4`: `1/√2` on `|0000⟩` and `|1111⟩`, and `0` elsewhere. -/
