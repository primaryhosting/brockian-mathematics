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

def lcaoSpan (n : ℕ) (ao : Fin n → V) : Submodule K V :=
  Submodule.span K (Set.range ao)

/-- Every molecular orbital is a linear combination of the atomic orbitals, and conversely. -/

theorem molecular_orbital_count (n : ℕ) (ao : Fin n → V) (h : LinearIndependent K ao) :
    Module.finrank K (lcaoSpan (K := K) n ao) = n := by
  rw [lcaoSpan, finrank_span_eq_card h, Fintype.card_fin]

/-- The `n` molecular orbitals themselves: a basis of the LCAO space indexed by `Fin n`,
so the molecular orbitals are in bijection with the atomic orbitals. -/
