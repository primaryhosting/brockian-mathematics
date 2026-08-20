import Mathlib

/-!
# Cnot Unitary Involutive
Category: Quantum Computing
Target: QC.cnot_unitary_involutive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix

/-- The controlled-NOT (CNOT) gate as a `4 × 4` complex matrix, in the
computational basis ordering `|00⟩, |01⟩, |10⟩, |11⟩`.  It leaves the target
qubit alone when the control qubit is `|0⟩` and flips it when the control
qubit is `|1⟩`. -/

theorem cnot_mem_unitaryGroup : cnot ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
  cnot_unitary_involutive.2.2.1

end QC

