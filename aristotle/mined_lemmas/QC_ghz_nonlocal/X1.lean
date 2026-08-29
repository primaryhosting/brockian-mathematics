import Mathlib

/-!
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- Computational basis labels for three qubits. -/
abbrev Three := Bool × Bool × Bool

/-- A (pure) state of three qubits: an amplitude for each computational basis label. -/
abbrev State := Three → ℂ

/-- The GHZ state `(|000⟩ + |111⟩)/√2`. -/

def X1 (ψ : State) : State := fun s => ψ (!s.1, s.2.1, s.2.2)
/-- Pauli `X` on the second qubit. -/
