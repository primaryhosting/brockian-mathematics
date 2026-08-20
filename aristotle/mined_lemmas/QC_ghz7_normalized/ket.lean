/-
# Ghz 7 Normalized
Category: Quantum Computing
Target: QC.ghz7_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

/-- The state space of 7 qubits: the (finite-dimensional) complex Hilbert space with
orthonormal basis indexed by bit strings `Fin 7 → Bool`. -/
abbrev Qubits7 : Type := EuclideanSpace ℂ (Fin 7 → Bool)

/-- The computational basis vector `|b⟩` associated with a bit string `b : Fin 7 → Bool`. -/

noncomputable def ket (b : Fin 7 → Bool) : Qubits7 := EuclideanSpace.single b (1 : ℂ)

/-- The 7-qubit GHZ state `(|0000000⟩ + |1111111⟩) / √2`. -/
