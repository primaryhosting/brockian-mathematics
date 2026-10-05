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

noncomputable def lcaoEquiv (n : ℕ) (ao : Fin n → V) (h : LinearIndependent K ao) :
    (Fin n → K) ≃ₗ[K] lcaoSpan (K := K) n ao :=
  (Finsupp.linearEquivFunOnFinite K K (Fin n)).symm.trans (moBasis n ao h).repr.symm

end Chem

