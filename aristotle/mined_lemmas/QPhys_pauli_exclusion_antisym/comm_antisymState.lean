/-
# Pauli Exclusion Antisym
Category: Quantum Physics
Target: QPhys.pauli_exclusion_antisym
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open TensorProduct

variable {H : Type*} [AddCommGroup H] [Module ℂ H]

/-- The antisymmetrized (fermionic) two-particle state built from single-particle
states `u` and `v`: `u ⊗ v - v ⊗ u`. -/

theorem comm_antisymState (u v : H) :
    TensorProduct.comm ℂ H H (antisymState u v) = -antisymState u v := by
  simp [antisymState, neg_sub]

/-- Exterior-algebra form of the exclusion principle: the wedge of a single-particle
state with itself is zero (`ExteriorAlgebra.ι_sq_zero`). -/
