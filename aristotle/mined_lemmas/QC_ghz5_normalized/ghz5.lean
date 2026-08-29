/-!
# Ghz 5 Normalized
Category: Quantum Computing
Target: QC.ghz5_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- Computational basis labels for 5 qubits: functions `Fin 5 → Bool`
(so the state space `EuclideanSpace ℂ (Fin 5 → Bool)` is the 32-dimensional
tensor product of five qubit spaces). -/
abbrev Qubits5 := Fin 5 → Bool

/-- The all-zeros label `|00000⟩`. -/

noncomputable def ghz5 : EuclideanSpace ℂ Qubits5 :=
  WithLp.toLp 2 (fun v => if v = allZero ∨ v = allOne then (1 / Real.sqrt 2 : ℝ) else 0)

/-- `ghz5` is indeed `(1/√2) • (|00000⟩ + |11111⟩)` in terms of the standard basis. -/
