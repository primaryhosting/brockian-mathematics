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

theorem pauli_exclusion_wavefunction {ι : Type*} (Ψ : ι → ι → ℂ)
    (hanti : ∀ x y, Ψ x y = - Ψ y x) (x : ι) :
    Ψ x x = 0 :=
  pauli_exclusion_antisym Ψ hanti x

/-- The Slater two-particle state is antisymmetric under exchange of the two particles. -/
