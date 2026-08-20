/-!
# Molecular Orbital Count
Category: Chemistry
Target: Chem.molecular_orbital_count
Statement: LCAO of n atomic orbitals yields exactly n molecular orbitals (dimension preservation).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

/-- **LCAO dimension preservation.**

A linear combination of atomic orbitals (LCAO) built from `n` linearly independent
atomic orbitals `atomicOrbital : Fin n → V` spans the space of molecular orbitals,
which has dimension exactly `n`: the number of molecular orbitals obtained equals
the number of atomic orbitals used.

The key Mathlib ingredient is `finrank_span_eq_card`. -/
theorem molecular_orbital_count
    {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    (n : ℕ) (atomicOrbital : Fin n → V)
    (hindep : LinearIndependent K atomicOrbital) :
    Module.finrank K (Submodule.span K (Set.range atomicOrbital)) = n := by
  simpa using finrank_span_eq_card hindep

end Chem


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

