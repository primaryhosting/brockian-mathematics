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

namespace QC

/-- The state space of three qubits: `ℂ^(2×2×2)` with the Euclidean (ℓ²) inner product. -/
abbrev Qubit3 : Type := EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2)

/-- The 3-qubit GHZ state `(|000⟩ + |111⟩)/√2`. -/

theorem ghz3_apply_one : ghz3 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 2)) = 1 / (Real.sqrt 2 : ℂ) := by
  simp [ghz3, EuclideanSpace.single_apply]

/-- All other amplitudes of the GHZ state vanish. -/
