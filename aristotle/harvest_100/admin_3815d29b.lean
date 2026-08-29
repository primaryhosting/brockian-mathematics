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

/-- **LCAO dimension preservation.**

Model: the electronic wavefunction space is a vector space `V` over a field `K`
(in practice `V` is a complex Hilbert space of one-electron wavefunctions).
A set of `n` atomic orbitals is a family `chi : Fin n → V`, assumed linearly
independent (a genuine, non-redundant AO basis set).  The molecular orbitals
produced by the LCAO method are exactly the linear combinations
`∑ i, c i • chi i`, i.e. the elements of `Submodule.span K (Set.range chi)`.

The theorem states that this MO space has dimension exactly `n`: LCAO of `n`
atomic orbitals yields exactly `n` (independent) molecular orbitals, and
moreover *every* basis of the MO space — i.e. every valid set of molecular
orbitals — is indexed by a type in bijection with `Fin n`, so it has exactly
`n` members.

The key Mathlib ingredient is `finrank_span_eq_card`. -/
theorem molecular_orbital_count
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (n : ℕ) (chi : Fin n → V) (hchi : LinearIndependent K chi) :
    Module.finrank K (Submodule.span K (Set.range chi)) = n ∧
      ∀ {ι : Type*}, Module.Basis ι K (Submodule.span K (Set.range chi)) →
        Nonempty (ι ≃ Fin n) := by
  have hdim : Module.finrank K (Submodule.span K (Set.range chi)) = n := by
    simpa using finrank_span_eq_card hchi
  refine ⟨hdim, ?_⟩
  intro ι mo
  have hfin : Module.Finite K (Submodule.span K (Set.range chi)) :=
    Module.Finite.span_of_finite K (Set.finite_range chi)
  have : Fintype ι := by
    classical
    exact Module.Basis.fintypeIndexOfRankLtAleph0 mo
      (by simpa using Module.rank_lt_aleph0 K (Submodule.span K (Set.range chi)))
  have hcard : Fintype.card ι = n := by
    rw [← hdim, Module.finrank_eq_card_basis mo]
  exact ⟨(Fintype.equivFinOfCardEq hcard)⟩

end Chem

