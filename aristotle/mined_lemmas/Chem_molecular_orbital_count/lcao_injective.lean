import Mathlib

/-!
# Molecular Orbital Count
Category: Chemistry
Target: Chem.molecular_orbital_count
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

namespace Chem

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The space of molecular orbitals obtained by the LCAO (linear combination of atomic
orbitals) procedure from a family `ao` of atomic orbitals: it is the span of the atomic
orbitals inside the ambient one-electron state space `V`. -/

theorem lcao_injective {n : ℕ} {ao : Fin n → V} (h : LinearIndependent K ao) :
    Function.Injective (lcao (K := K) ao) := by
  simpa [lcao] using h.fintypeLinearCombination_injective

/-- **Molecular orbital count.** The LCAO procedure applied to `n` linearly independent
atomic orbitals produces a space of molecular orbitals of dimension exactly `n`:
`n` atomic orbitals yield `n` molecular orbitals (dimension preservation). -/
