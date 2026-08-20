import Mathlib

/-!
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

/-! ## The three-qubit Hilbert space -/

/-- Computational basis index for three qubits. -/
abbrev Q : Type := Fin 2 × Fin 2 × Fin 2

/-- The Pauli `X` matrix. -/

def LHV.MerminConstraints (v : LHV) : Prop :=
  v.x 0 * v.y 1 * v.y 2 = -1 ∧
  v.y 0 * v.x 1 * v.y 2 = -1 ∧
  v.y 0 * v.y 1 * v.x 2 = -1 ∧
  v.x 0 * v.x 1 * v.x 2 = 1

/-- No local hidden-variable assignment can reproduce all four GHZ predictions:
multiplying the three `-1` relations gives `x₀x₁x₂ = -1`, contradicting `x₀x₁x₂ = +1`. -/
