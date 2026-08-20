/-
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
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

/-- Bit flip on a single (qu)bit index. -/

theorem postMeasure_ne_of_no_correction :
    ∃ psi : Fin 2 → ℂ, postMeasure psi 1 0 ≠ psi := by
  refine ⟨![0, 1], fun h => ?_⟩
  have h1 := congrFun h 1
  simp [postMeasure, initialState, bellBasis, bell, Fin.sum_univ_succ] at h1
  rw [sqrt_two_inv_sq] at h1
  norm_num at h1

end QC

