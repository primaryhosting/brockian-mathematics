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

namespace Chem

/-- The molecular orbitals produced by the LCAO (Linear Combination of Atomic Orbitals)
method: given `n` atomic orbitals `phi j` in a complex vector space of states and a
coefficient matrix `C`, the `i`-th molecular orbital is `∑ j, C i j • phi j`. -/
noncomputable def lcao {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (C : Matrix (Fin n) (Fin n) ℂ) (phi : Fin n → V) : Fin n → V :=
  fun i => ∑ j, C i j • phi j

/-- **LCAO preserves dimension**: `n` linearly independent atomic orbitals `phi`, combined
through an invertible coefficient matrix `C`, yield exactly `n` molecular orbitals.

Formally, the family `lcao C phi` of `n` molecular orbitals is linearly independent, it spans
exactly the same space as the atomic orbitals do, and that space has dimension `n`. Thus no
orbitals are created or destroyed by the linear combination step: `n` atomic orbitals in,
`n` molecular orbitals out. -/
theorem molecular_orbital_count {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (phi : Fin n → V) (hphi : LinearIndependent ℂ phi)
    (C : Matrix (Fin n) (Fin n) ℂ) (hC : IsUnit C.det) :
    LinearIndependent ℂ (lcao C phi) ∧
      Submodule.span ℂ (Set.range (lcao C phi)) = Submodule.span ℂ (Set.range phi) ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range (lcao C phi))) = n := by
  classical
  set psi : Fin n → V := lcao C phi with hpsidef
  have hpsi : ∀ i, psi i = ∑ j, C i j • phi j := fun i => rfl
  set L : (Fin n → ℂ) →ₗ[ℂ] V := Fintype.linearCombination ℂ phi with hL
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro m hm
    have := (Fintype.linearIndependent_iff.mp hphi) m
      (by simpa [hL, Fintype.linearCombination_apply] using hm)
    funext i
    simpa using this i
  have hrows : LinearIndependent ℂ C.row :=
    Matrix.linearIndependent_rows_of_isUnit ((Matrix.isUnit_iff_isUnit_det C).mpr hC)
  have hcomp : psi = ⇑L ∘ C.row := by
    funext i
    simp [hpsi i, hL, Fintype.linearCombination_apply, Matrix.row]
  have hind : LinearIndependent ℂ psi := by
    rw [hcomp]
    exact hrows.map' L hker
  have hrank : Module.finrank ℂ (Submodule.span ℂ (Set.range psi)) = n := by
    simpa using finrank_span_eq_card hind
  have hrank' : Module.finrank ℂ (Submodule.span ℂ (Set.range phi)) = n := by
    simpa using finrank_span_eq_card hphi
  have hle : Submodule.span ℂ (Set.range psi) ≤ Submodule.span ℂ (Set.range phi) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [hpsi i]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range phi)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range phi)
  exact ⟨hind, Submodule.eq_of_le_of_finrank_eq hle (by rw [hrank, hrank']), hrank⟩

/-- Corollary: the `n` molecular orbitals form a basis of the space spanned by the atomic
orbitals, so they are exactly `n` in number and describe the same space. -/
theorem molecular_orbital_basis {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (phi : Fin n → V) (hphi : LinearIndependent ℂ phi)
    (C : Matrix (Fin n) (Fin n) ℂ) (hC : IsUnit C.det) :
    Nonempty (Module.Basis (Fin n) ℂ (Submodule.span ℂ (Set.range phi))) := by
  obtain ⟨hind, hspan, -⟩ := molecular_orbital_count phi hphi C hC
  exact ⟨hspan ▸ Module.Basis.span hind⟩

end Chem

