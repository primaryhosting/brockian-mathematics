import Mathlib

/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
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

open Complex

/-- A normalized qubit state vector: a unit vector in `ℂ²`. -/

lemma blochQubit_phase_invariant (v w : Qubit) (h : v ≈ w) : blochQubit v = blochQubit w := by
  obtain ⟨c, hc, hw⟩ := h
  apply Subtype.ext
  show blochVec v.val = blochVec w.val
  rw [show w.val = (c * v.val.1, c * v.val.2) from hw, blochVec_phase _ _ _ hc]

/-- The Bloch map: pure qubit states (unit vectors mod global phase) to points of `S²`. -/
