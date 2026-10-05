import Mathlib

/-!
# Hadamard Involutive
Category: Quantum Computing
Target: QC.hadamard_involutive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix Complex

/-- The normalization constant `1/√2` of the Hadamard gate, as a complex number. -/

noncomputable def hc : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

/-- The single-qubit Hadamard gate `H = (1/√2) • !![1, 1; 1, -1]`. -/
