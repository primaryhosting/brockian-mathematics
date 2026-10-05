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

/-- The space of molecular orbitals produced by the LCAO (Linear Combination of Atomic
Orbitals) method from a family of atomic orbitals `chi : Fin n → H`: it is the set of all
linear combinations `∑ i, c i • chi i` of the atomic orbitals, i.e. their complex span
inside the one-electron Hilbert space `H`. -/
noncomputable def lcaoSpace {H : Type*} [AddCommGroup H] [Module ℂ H]
    {n : ℕ} (chi : Fin n → H) : Submodule ℂ H :=
  Submodule.span ℂ (Set.range chi)

/-- Every element of the LCAO space is indeed a linear combination of the atomic orbitals
(with complex coefficients), justifying the name. -/
theorem mem_lcaoSpace_iff {H : Type*} [AddCommGroup H] [Module ℂ H]
    {n : ℕ} (chi : Fin n → H) (psi : H) :
    psi ∈ lcaoSpace chi ↔ ∃ c : Fin n → ℂ, psi = ∑ i, c i • chi i := by
  classical
  constructor
  · intro hpsi
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hpsi
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun ℂ).2 ⟨c, rfl⟩

/-- **Molecular orbital count.**  The LCAO method applied to `n` linearly independent
atomic orbitals `chi : Fin n → H` yields exactly `n` molecular orbitals: the space of
their linear combinations has complex dimension `n`, so any basis of molecular orbitals
for it consists of exactly `n` orbitals (dimension preservation, "n AOs in, n MOs out").

The key Mathlib ingredient is `finrank_span_eq_card`. -/
theorem molecular_orbital_count {H : Type*} [AddCommGroup H] [Module ℂ H]
    {n : ℕ} (chi : Fin n → H) (hchi : LinearIndependent ℂ chi) :
    Module.finrank ℂ (lcaoSpace chi) = n := by
  simpa [lcaoSpace] using finrank_span_eq_card hchi

/-- Restatement in terms of an actual basis of molecular orbitals: if `mo` is any basis of
the LCAO space indexed by a type `ι`, then `ι` has exactly `n` elements, i.e. there are
exactly `n` molecular orbitals. -/
theorem card_molecular_orbital_basis {H : Type*} [AddCommGroup H] [Module ℂ H]
    {n : ℕ} (chi : Fin n → H) (hchi : LinearIndependent ℂ chi)
    {ι : Type*} [Fintype ι] (mo : Module.Basis ι ℂ (lcaoSpace chi)) :
    Fintype.card ι = n := by
  rw [← Module.finrank_eq_card_basis mo]
  exact molecular_orbital_count chi hchi

end Chem

