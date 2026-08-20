import Mathlib

/-!
# Ghz 7 Normalized
Category: Quantum Computing
Target: QC.ghz7_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

/-- Computational basis states of 7 qubits: functions `Fin 7 → Bool`. -/
abbrev Qubits7 := Fin 7 → Bool

/-- The all-zeros basis state `|0000000⟩`. -/

noncomputable def ghz7 : EuclideanSpace ℂ Qubits7 :=
  WithLp.toLp 2 (fun x => if x = allZero then (Real.sqrt 2)⁻¹
    else if x = allOne then (Real.sqrt 2)⁻¹ else 0)

