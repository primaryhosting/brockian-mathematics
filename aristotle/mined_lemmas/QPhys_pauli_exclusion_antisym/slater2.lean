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

noncomputable def slater2 {V : Type*} [AddCommGroup V] [Module ℂ V] (psi phi : V) : V ⊗[ℂ] V :=
  psi ⊗ₜ[ℂ] phi - phi ⊗ₜ[ℂ] psi

/-- **Pauli exclusion principle (antisymmetry form).**
A two-fermion state `Ψ`, valued in a complex vector space and antisymmetric under
exchange of the two particle labels (`Ψ x y = - Ψ y x`), vanishes when both fermions
occupy the same single-particle state `x`. -/
