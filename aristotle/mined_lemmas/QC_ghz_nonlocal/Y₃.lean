/-
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- A pure state of three qubits, written in the computational basis indexed by
`Bool × Bool × Bool` (`false = |0⟩`, `true = |1⟩`). -/
abbrev State := Bool × Bool × Bool → ℂ

/-- Pauli `X` acting on the first qubit. -/

def Y₃ (f : State) : State :=
  fun p => (if p.2.2 then Complex.I else -Complex.I) * f (p.1, p.2.1, !p.2.2)

/-- The GHZ state `(|000⟩ + |111⟩)/√2`. -/
