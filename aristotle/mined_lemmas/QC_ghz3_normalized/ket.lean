import Mathlib

/-!
# Ghz 3 Normalized
Category: Quantum Computing
Target: QC.ghz3_normalized
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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false


namespace QC

/-- The state space of three qubits: `ℂ^(2×2×2)` with the Euclidean (Hermitian) norm. -/
abbrev Qubits3 := EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2)

/-- The computational basis ket `|v⟩` for a bit-triple `v`. -/

noncomputable def ket (v : Fin 2 × Fin 2 × Fin 2) : Qubits3 := EuclideanSpace.single v 1

/-- The 3-qubit GHZ state `(|000⟩ + |111⟩)/√2`. -/
