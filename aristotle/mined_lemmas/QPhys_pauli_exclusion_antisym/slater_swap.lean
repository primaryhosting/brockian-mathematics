import Mathlib

/-!
# Pauli Exclusion Antisym
Category: Quantum Physics
Target: QPhys.pauli_exclusion_antisym
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped TensorProduct

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

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- The (unnormalized) antisymmetric two-fermion state built from the two
single-particle states `u` and `f`: the Slater determinant
`u ⊗ f - f ⊗ u` inside the two-particle space `V ⊗ V`. -/

theorem slater_swap (u f : V) : slater (K := K) f u = - slater (K := K) u f := by
  simp [slater]

/-- **Pauli exclusion principle.** A two-fermion antisymmetric state whose two
single-particle states coincide is the zero state. -/
