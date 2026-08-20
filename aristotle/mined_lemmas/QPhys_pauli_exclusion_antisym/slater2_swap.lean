/-
# Pauli Exclusion Antisym
Category: Quantum Physics
Target: QPhys.pauli_exclusion_antisym
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QPhys

open TensorProduct

/-- The (unnormalized) two-fermion Slater state built from single-particle states
`psi` and `chi`: the antisymmetrization `psi ⊗ chi - chi ⊗ psi` inside the two-particle
Hilbert space `V ⊗ V`. -/

theorem slater2_swap {𝕜 V : Type*} [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (psi chi : V) : slater2 (𝕜 := 𝕜) chi psi = - slater2 (𝕜 := 𝕜) psi chi := by
  simp [slater2]

/-- **Pauli exclusion principle (antisymmetry form).**
A two-fermion antisymmetric state with equal single-particle states is zero:
the antisymmetrized state `psi ⊗ psi - psi ⊗ psi` vanishes, and more generally any
exchange-antisymmetric two-particle wave function `Psi` (valued in a complex
vector space) vanishes on the diagonal. -/
