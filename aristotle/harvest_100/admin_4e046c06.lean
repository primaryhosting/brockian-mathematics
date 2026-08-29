/-
# Molecular Orbital Count
Category: Chemistry
Target: Chem.molecular_orbital_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Molecular Orbital Count
Category: Chemistry
Target: Chem.molecular_orbital_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- **LCAO dimension preservation.**

A linear combination of atomic orbitals (LCAO) built from `n` linearly independent atomic
orbitals `ao 0, …, ao (n-1)` via an invertible coefficient matrix `C` (i.e.
`mo i = ∑ j, C i j • ao j`) yields exactly `n` molecular orbitals: the family `mo` is
linearly independent, it spans the same space as the atomic orbitals, and that space has
dimension exactly `n`.  Thus no orbitals are created or destroyed by the LCAO procedure. -/
theorem molecular_orbital_count
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (ao : Fin n → V) (hao : LinearIndependent K ao)
    (C : Matrix (Fin n) (Fin n) K) (hC : IsUnit C.det)
    (mo : Fin n → V) (hmo : ∀ i, mo i = ∑ j, C i j • ao j) :
    LinearIndependent K mo ∧
      Submodule.span K (Set.range mo) = Submodule.span K (Set.range ao) ∧
      Module.finrank K (Submodule.span K (Set.range mo)) = n := by
  set W := Submodule.span K (Set.range ao) with hW
  let b : Module.Basis (Fin n) K W := Module.Basis.span hao
  have hb : ∀ i, (b i : V) = ao i := fun i => Module.Basis.span_apply hao i
  have hmoW : ∀ i, mo i ∈ W := by
    intro i
    rw [hmo i]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨j, rfl⟩)
  let mo' : Fin n → W := fun i => ⟨mo i, hmoW i⟩
  have hmo' : ∀ i, mo' i = ∑ j, C i j • b j := by
    intro i
    apply Subtype.ext
    push_cast
    simp [mo', hmo i, hb]
  have hrepr : ∀ i j, b.repr (mo' i) j = C i j := by
    intro i j
    rw [hmo' i]
    simp [Finsupp.single_apply, eq_comm]
  have hdet : b.det mo' = C.det := by
    rw [Module.Basis.det_apply]
    have hT : b.toMatrix mo' = C.transpose := by
      ext i j
      simp [Module.Basis.toMatrix_apply, hrepr, Matrix.transpose_apply]
    rw [hT, Matrix.det_transpose]
  have hbasis := (Module.Basis.is_basis_iff_det b).mpr (hdet ▸ hC)
  have hspan : Submodule.span K (Set.range mo) = W := by
    have h1 : Submodule.map W.subtype (Submodule.span K (Set.range mo')) = W := by
      rw [hbasis.2, Submodule.map_subtype_top]
    rw [Submodule.map_span] at h1
    have h2 : ⇑W.subtype '' (Set.range mo') = Set.range mo := by
      ext x
      simp [mo', Set.mem_range]
    rwa [h2] at h1
  refine ⟨hbasis.1.map' W.subtype W.ker_subtype, hspan, ?_⟩
  rw [hspan]
  simpa using Module.finrank_eq_card_basis b

end Chem

import Mathlib

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

