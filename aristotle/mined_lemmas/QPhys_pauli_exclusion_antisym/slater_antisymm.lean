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

/-- The (unnormalized) two-fermion Slater state built from two single-particle
states `ψ` and `χ`: the antisymmetrized tensor product `ψ ⊗ χ - χ ⊗ ψ`. -/

theorem slater_antisymm {H : Type*} [AddCommGroup H] [Module ℂ H] (ψ χ : H) :
    slater ψ χ = - slater χ ψ := by
  simp [slater]

/-- **Pauli exclusion principle (antisymmetry form).**

Any antisymmetric two-particle state vanishes when the two single-particle states
coincide.  Concretely, if `Ψ` is a `ℂ`-bilinear two-particle amplitude (valued in an
arbitrary complex vector space `W`, so this covers both scalar wavefunctions and
tensor-product-valued states) which is antisymmetric under exchange of the two
particles, then `Ψ ψ ψ = 0` for every single-particle state `ψ`. -/
