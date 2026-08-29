/-
# Point Group Finite O 3
Category: Chemistry
Target: Chem.point_group_finite_O3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Chem

open Matrix

/-- The orthogonal group `O(3)`: the group of real `3 × 3` matrices `A` with `Aᵀ * A = 1`,
acting on Euclidean three-space `Fin 3 → ℝ`. -/
abbrev O3 : Submonoid (Matrix (Fin 3) (Fin 3) ℝ) :=
  Matrix.orthogonalGroup (Fin 3) ℝ

/-- The action of an element of `O(3)` on a point of Euclidean three-space. -/
def act (A : O3) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (A : Matrix (Fin 3) (Fin 3) ℝ).mulVec x

lemma act_one (x : Fin 3 → ℝ) : act 1 x = x := by
  simp [act, Matrix.one_mulVec]

lemma act_mul (A B : O3) (x : Fin 3 → ℝ) : act (A * B) x = act A (act B x) := by
  simp [act, Matrix.mulVec_mulVec]

/-- The point group of a molecule whose atoms occupy the positions `S`: the group of all
orthogonal transformations of space mapping the set of atomic positions onto itself.
By construction it is a subgroup of `O(3)`. -/
def pointGroup (S : Finset (Fin 3 → ℝ)) : Subgroup O3 where
  carrier := {A | S.image (act A) = S}
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    ext x
    simp [act_one]
  mul_mem' := by
    intro A B hA hB
    simp only [Set.mem_setOf_eq] at hA hB ⊢
    have h : S.image (act (A * B)) = (S.image (act B)).image (act A) := by
      rw [Finset.image_image]
      exact Finset.image_congr (by intro x _; simp [act_mul])
    rw [h, hB, hA]
  inv_mem' := by
    intro A hA
    simp only [Set.mem_setOf_eq] at hA ⊢
    have hcomp : ∀ x, act A⁻¹ (act A x) = x := by
      intro x
      rw [← act_mul]
      simp [act_one]
    calc S.image (act A⁻¹) = (S.image (act A)).image (act A⁻¹) := by rw [hA]
      _ = S.image (fun x => act A⁻¹ (act A x)) := by rw [Finset.image_image]; rfl
      _ = S := by simp [hcomp]

/-- **Every molecular point group is a finite subgroup of `O(3)`.**

The point group of a molecule is by construction a subgroup of `O(3)` (see `Chem.pointGroup`);
the content of the theorem is that it is *finite*, whenever the atomic positions `S` are
non-degenerate, i.e. they span all of three-dimensional space.  (Some such hypothesis is
necessary: a *linear* molecule has the infinite point group `C∞ᵥ` or `D∞ₕ`.)

The proof is the standard one: a symmetry operation permutes the finitely many atoms, and a
linear map is determined by its values on a spanning set, so the point group embeds into the
finite group of permutations of the atoms. -/
theorem point_group_finite_O3 (S : Finset (Fin 3 → ℝ))
    (hS : Submodule.span ℝ (S : Set (Fin 3 → ℝ)) = ⊤) :
    Finite (pointGroup S) := by
  have hmem : ∀ (A : pointGroup S) (x : {y // y ∈ S}), act (A : O3) (x : Fin 3 → ℝ) ∈ S := by
    intro A x
    have hA : S.image (act (A : O3)) = S := A.2
    have h1 : act (A : O3) (x : Fin 3 → ℝ) ∈ S.image (act (A : O3)) :=
      Finset.mem_image_of_mem _ x.2
    rwa [hA] at h1
  -- the map sending a symmetry operation to the induced permutation of the atoms
  set F : (pointGroup S) → ({y // y ∈ S} → {y // y ∈ S}) :=
    fun A x => ⟨act (A : O3) (x : Fin 3 → ℝ), hmem A x⟩ with hF
  have hinj : Function.Injective F := by
    intro A B hAB
    have hval : ∀ x ∈ S, act (A : O3) x = act (B : O3) x := by
      intro x hx
      have := congrArg (fun f => (f ⟨x, hx⟩ : Fin 3 → ℝ)) hAB
      simpa [hF] using this
    -- two linear maps agreeing on a spanning set are equal
    have hlin : Matrix.toLin' ((A : O3) : Matrix (Fin 3) (Fin 3) ℝ)
        = Matrix.toLin' ((B : O3) : Matrix (Fin 3) (Fin 3) ℝ) := by
      apply LinearMap.ext_on hS
      intro x hx
      simpa [Matrix.toLin'_apply, act] using hval x hx
    have hmat : ((A : O3) : Matrix (Fin 3) (Fin 3) ℝ) = ((B : O3) : Matrix (Fin 3) (Fin 3) ℝ) :=
      Matrix.toLin'.injective hlin
    exact Subtype.ext (Subtype.ext hmat)
  exact Finite.of_injective F hinj

/-- The non-degeneracy hypothesis of `Chem.point_group_finite_O3` is satisfiable: there are
configurations of atomic positions spanning three-dimensional space, so the theorem is not
vacuous. -/
theorem exists_nondegenerate_positions :
    ∃ S : Finset (Fin 3 → ℝ), Submodule.span ℝ (S : Set (Fin 3 → ℝ)) = ⊤ := by
  refine ⟨Finset.univ.image (fun i : Fin 3 => (Pi.basisFun ℝ (Fin 3)) i), ?_⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact (Pi.basisFun ℝ (Fin 3)).span_eq

end Chem

