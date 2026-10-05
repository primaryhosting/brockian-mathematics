/-
# Pauli Exclusion Antisym
Category: Quantum Physics
Target: QPhys.pauli_exclusion_antisym
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` commands to precede any module docstring, so the header
-- above is written as a plain block comment and repeated as a module docstring below.)

import Mathlib

/-!
# Pauli Exclusion Antisym
Category: Quantum Physics
Target: QPhys.pauli_exclusion_antisym
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open scoped TensorProduct

/-- The antisymmetrized (Slater) two-particle state built from two single-particle
states `psi` and `phi` of a complex vector space `V`:
`slater2 psi phi = psi ⊗ phi - phi ⊗ psi ∈ V ⊗ V`. -/

theorem slater2_antisymm {V : Type*} [AddCommGroup V] [Module ℂ V] (psi phi : V) :
    slater2 psi phi = - slater2 phi psi := by
  simp [slater2]

/-- The Slater determinant state of two fermions occupying the *same* single-particle
state vanishes: two identical fermions cannot occupy the same state. -/
