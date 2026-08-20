/-
# Ghz 5 Normalized
Category: Quantum Computing
Target: QC.ghz5_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Classical

namespace QC

/-- Computational basis states of 5 qubits are indexed by `Fin 5 → Bool`; the state space is
the Hilbert space `EuclideanSpace ℂ (Fin 5 → Bool)` (dimension `2^5 = 32`). -/
abbrev Qubits5 := EuclideanSpace ℂ (Fin 5 → Bool)

/-- The 5-qubit GHZ state `(|00000⟩ + |11111⟩)/√2`. -/

noncomputable def ghz5 : Qubits5 :=
  WithLp.toLp 2 fun b =>
    if b = (fun _ => false) ∨ b = (fun _ => true) then (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0

/-- The 5-qubit GHZ state is a unit vector. -/
