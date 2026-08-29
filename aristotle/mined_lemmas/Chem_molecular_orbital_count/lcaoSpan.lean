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
