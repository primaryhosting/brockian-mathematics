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

theorem slater2_self_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V] (psi : V) :
    slater2 psi psi = 0 :=
  pauli_exclusion_antisym (M := V ⊗[ℂ] V) slater2 slater2_antisymm psi

end QPhys

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

