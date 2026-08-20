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

noncomputable def moBasis {n : ℕ} {ao : Fin n → V} (h : LinearIndependent K ao) :
    Module.Basis (Fin n) K (moSpace (K := K) ao) :=
  Module.Basis.span h

/-- The coefficient space `Fin n → K` of LCAO coefficients is linearly isomorphic to the
molecular-orbital space, when the atomic orbitals are linearly independent. -/
