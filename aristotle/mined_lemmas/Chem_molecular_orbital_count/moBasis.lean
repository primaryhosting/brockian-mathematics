/-
# Molecular Orbital Count
Category: Chemistry
Target: Chem.molecular_orbital_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The space of molecular orbitals obtained by the LCAO (Linear Combination of Atomic
Orbitals) method from a family `ao` of `n` atomic orbitals: it is the space of all linear
combinations `∑ i, c i • ao i` of the atomic orbitals, i.e. their span. -/

noncomputable def moBasis (n : ℕ) (ao : Fin n → V) (h : LinearIndependent K ao) :
    Module.Basis (Fin n) K (lcaoSpan (K := K) n ao) :=
  Module.Basis.span h

/-- The coefficient space `Fin n → K` of LCAO coefficients is linearly isomorphic to the
space of molecular orbitals: distinct coefficient vectors give distinct molecular orbitals
and every molecular orbital arises this way. -/
