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

def tri (A B C : Matrix (Fin 2) (Fin 2) ℂ) : Matrix Q Q ℂ :=
  fun i j => A i.1 j.1 * B i.2.1 j.2.1 * C i.2.2 j.2.2

/-- The (unnormalised) GHZ state `|000⟩ + |111⟩`. -/
