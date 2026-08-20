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

universe u v w

open Module

/-- **LCAO dimension preservation.**

Model: the atomic orbitals are `n` linearly independent vectors `chi 0, …, chi (n-1)`
of a `K`-vector space `V` of one-electron wavefunctions.  A linear combination of atomic
orbitals (LCAO) is described by a coefficient matrix `C` whose rows give the molecular
orbitals `psi i = ∑ j, C i j • chi j`; the LCAO ansatz is non-degenerate exactly when `C`
is invertible.

Conclusions:

1. the `n` molecular orbitals produced are linearly independent (none of them is redundant);
2. they span exactly the same space as the atomic orbitals (the LCAO space is preserved);
3. that space has dimension `n`;
4. consequently *every* set of molecular orbitals forming a basis of the LCAO space has
   exactly `n` elements: `n` atomic orbitals yield exactly `n` molecular orbitals. -/
theorem molecular_orbital_count
    {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (n : ℕ) (chi : Fin n → V) (hchi : LinearIndependent K chi)
    (C : Matrix (Fin n) (Fin n) K) (hC : IsUnit C.det)
    (psi : Fin n → V) (hpsi : ∀ i, psi i = ∑ j, C i j • chi j) :
    LinearIndependent K psi ∧
      Submodule.span K (Set.range psi) = Submodule.span K (Set.range chi) ∧
      Module.finrank K (Submodule.span K (Set.range chi) : Submodule K V) = n ∧
      ∀ (ι : Type w) [Fintype ι],
        Basis ι K (Submodule.span K (Set.range chi) : Submodule K V) →
          Fintype.card ι = n := by
  classical
  set S : Submodule K V := Submodule.span K (Set.range chi) with hS
  -- the atomic orbitals form a basis of the space `S` they span
  let B : Basis (Fin n) K S := Basis.span hchi
  -- the LCAO coefficient matrix induces a linear automorphism of `S`
  have hCt : IsUnit (C.transpose).det := by simpa [Matrix.det_transpose] using hC
  let e : S ≃ₗ[K] S := Matrix.toLinearEquiv B C.transpose hCt
  let B' : Basis (Fin n) K S := B.map e
  have hB' : ∀ i, (B' i : V) = psi i := by
    intro i
    have h1 : B' i = ∑ j, C i j • B j := by
      show e (B i) = _
      rw [Matrix.toLinearEquiv_apply, Matrix.toLin_self]
      simp [Matrix.transpose_apply]
    have h2 : ((∑ j, C i j • B j : S) : V) = ∑ j, C i j • chi j := by
      push_cast
      exact Finset.sum_congr rfl fun j _ => by rw [Basis.span_apply hchi j]
    rw [h1, h2, hpsi i]
  -- (1) linear independence of the molecular orbitals
  have hli : LinearIndependent K psi := by
    have h := B'.linearIndependent.map' S.subtype (by simp)
    have : (S.subtype ∘ B') = psi := funext fun i => hB' i
    rwa [this] at h
  refine ⟨hli, ?_, ?_, ?_⟩
  · -- (2) the span is unchanged
    have hrange : Set.range psi = S.subtype '' (Set.range B') := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext fun i => (hB' i).symm)
    rw [hrange, Submodule.span_image, B'.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  · -- (3) the LCAO space has dimension `n`
    simpa using finrank_span_eq_card hchi
  · -- (4) hence any basis of the LCAO space has exactly `n` elements
    intro ι _ b
    have h1 : Module.finrank K (S : Submodule K V) = Fintype.card ι :=
      Module.finrank_eq_card_basis b
    have h2 : Module.finrank K (S : Submodule K V) = n := by
      simpa using finrank_span_eq_card hchi
    omega

end Chem

