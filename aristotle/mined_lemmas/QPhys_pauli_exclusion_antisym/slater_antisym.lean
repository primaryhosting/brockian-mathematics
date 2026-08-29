/-
# Pauli Exclusion Antisym
Category: Quantum Physics
Target: QPhys.pauli_exclusion_antisym
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- **Pauli exclusion principle (antisymmetry form).**

A two-fermion state is described by a map `psi : ι → ι → V` assigning to each pair of
single-particle labels `i j` an amplitude in a complex vector space `V`, subject to the
antisymmetry (exchange) condition `psi i j = - psi j i`.

If the two fermions occupy the *same* single-particle state `i`, the amplitude vanishes:
`psi i i = 0`.  Equivalently (contrapositive): a nonzero amplitude forces the two
single-particle states to be distinguishable. -/

theorem slater_antisym {ι : Type*} (f g : ι → ℂ) (i j : ι) :
    slater f g i j = -slater f g j i := by
  simp only [slater]; ring

/-- Pauli exclusion for a Slater determinant: the amplitude for both fermions to occupy the
same single-particle state vanishes. -/
