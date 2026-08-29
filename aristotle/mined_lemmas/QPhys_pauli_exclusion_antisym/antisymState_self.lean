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

theorem antisymState_self (ψ : H) : antisymState ψ ψ = 0 := sub_self _

/-- The antisymmetrized state is indeed antisymmetric under particle exchange. -/
