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

theorem mem_lcaoSpan_iff (n : ℕ) (ao : Fin n → V) (v : V) :
    v ∈ lcaoSpan (K := K) n ao ↔ ∃ c : Fin n → K, ∑ i, c i • ao i = v :=
  Submodule.mem_span_range_iff_exists_fun K

/-- **LCAO dimension preservation.**  A linear combination of `n` (linearly independent)
atomic orbitals yields a space of molecular orbitals of dimension exactly `n`: the LCAO
procedure produces exactly `n` molecular orbitals. -/
