/-
# Point Group Finite O 3
Category: Chemistry
Target: Chem.point_group_finite_O3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Point Group Finite O 3
Category: Chemistry
Target: Chem.point_group_finite_O3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Chem

open Matrix

/-- The point group of a molecule, modelled as a finite set `S` of atomic positions in
`ℝ³`: it is the subgroup of the orthogonal group `O(3)` consisting of those orthogonal
transformations that map the molecule onto itself. -/
def pointGroup (S : Finset (Fin 3 → ℝ)) : Subgroup (Matrix.orthogonalGroup (Fin 3) ℝ) where
  carrier := {A | ∀ x, x ∈ S ↔ (A : Matrix (Fin 3) (Fin 3) ℝ).mulVec x ∈ S}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro A B hA hB x
    have : ((A * B : Matrix.orthogonalGroup (Fin 3) ℝ) :
        Matrix (Fin 3) (Fin 3) ℝ).mulVec x
        = (A : Matrix (Fin 3) (Fin 3) ℝ).mulVec
            ((B : Matrix (Fin 3) (Fin 3) ℝ).mulVec x) := by
      simp [Matrix.mulVec_mulVec]
    rw [this, ← hA, ← hB]
  inv_mem' := by
    intro A hA x
    have hinv : ((A⁻¹ : Matrix.orthogonalGroup (Fin 3) ℝ) :
        Matrix (Fin 3) (Fin 3) ℝ).mulVec x ∈ S ↔ x ∈ S := by
      rw [hA (((A⁻¹ : Matrix.orthogonalGroup (Fin 3) ℝ) :
        Matrix (Fin 3) (Fin 3) ℝ).mulVec x), Matrix.mulVec_mulVec]
      have : (A : Matrix (Fin 3) (Fin 3) ℝ) *
          ((A⁻¹ : Matrix.orthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
        rw [← Submonoid.coe_mul, ← Units.val_one]
        norm_cast
        simp
      rw [this, Matrix.one_mulVec]
    exact hinv.symm

/-- Two elements of the point group that act identically on a spanning set of atomic
positions are equal. -/
theorem pointGroup_ext_of_span {S : Finset (Fin 3 → ℝ)}
    (hspan : Submodule.span ℝ (S : Set (Fin 3 → ℝ)) = ⊤)
    {A B : Matrix.orthogonalGroup (Fin 3) ℝ}
    (h : ∀ x ∈ S, (A : Matrix (Fin 3) (Fin 3) ℝ).mulVec x
      = (B : Matrix (Fin 3) (Fin 3) ℝ).mulVec x) : A = B := by
  have hlin : Matrix.mulVecLin (A : Matrix (Fin 3) (Fin 3) ℝ)
      = Matrix.mulVecLin (B : Matrix (Fin 3) (Fin 3) ℝ) :=
    LinearMap.ext_on hspan (fun x hx => h x hx)
  have : (A : Matrix (Fin 3) (Fin 3) ℝ) = (B : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    have := congrFun (congrArg (fun f => f (Pi.single j (1 : ℝ))) hlin) i
    simpa [Matrix.mulVec_single] using this
  exact Subtype.ext this

/-- The action of a point-group element on the atoms of the molecule: a symmetry
operation permutes the atomic positions. -/
def atomMap (S : Finset (Fin 3 → ℝ)) (A : pointGroup S) : {y // y ∈ S} → {y // y ∈ S} :=
  fun x => ⟨((A : Matrix.orthogonalGroup (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ).mulVec (x : Fin 3 → ℝ), (A.2 (x : Fin 3 → ℝ)).1 x.2⟩

/-- If the atoms span `ℝ³`, a symmetry operation is determined by the permutation it
induces on the atoms. -/
theorem atomMap_injective {S : Finset (Fin 3 → ℝ)}
    (hspan : Submodule.span ℝ (S : Set (Fin 3 → ℝ)) = ⊤) :
    Function.Injective (atomMap S) := by
  intro A B hAB
  apply Subtype.ext
  refine pointGroup_ext_of_span hspan (fun x hx => ?_)
  exact congrArg Subtype.val (congrFun hAB ⟨x, hx⟩)

/-- **Every molecular point group is a finite subgroup of `O(3)`.**

A molecule is given by a finite set `S` of atomic positions in `ℝ³` which spans `ℝ³`
(i.e. the molecule is not contained in a plane through the origin, so the geometry
determines the symmetry operations).  Its point group `pointGroup S` is by construction a
subgroup of the orthogonal group `O(3) = Matrix.orthogonalGroup (Fin 3) ℝ`, and this
subgroup is finite: a symmetry operation permutes the atoms, and since the atoms span
`ℝ³` it is determined by that permutation. -/
theorem point_group_finite_O3 (S : Finset (Fin 3 → ℝ))
    (hspan : Submodule.span ℝ (S : Set (Fin 3 → ℝ)) = ⊤) :
    Finite (pointGroup S) :=
  Finite.of_injective (atomMap S) (atomMap_injective hspan)

/-- A quantitative form: the order of a molecular point group is at most `n ^ n`, where
`n` is the number of atoms. -/
theorem point_group_card_le (S : Finset (Fin 3 → ℝ))
    (hspan : Submodule.span ℝ (S : Set (Fin 3 → ℝ)) = ⊤) :
    Nat.card (pointGroup S) ≤ S.card ^ S.card := by
  have := Nat.card_le_card_of_injective (atomMap S) (atomMap_injective hspan)
  simpa [Nat.card_eq_fintype_card, Fintype.card_fun] using this

/-- The elements of a point group really are orthogonal transformations: they preserve
the Euclidean inner product on `ℝ³`. -/
theorem pointGroup_dotProduct (S : Finset (Fin 3 → ℝ)) (A : pointGroup S)
    (x y : Fin 3 → ℝ) :
    (((A : Matrix.orthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ).mulVec x) ⬝ᵥ
        (((A : Matrix.orthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ).mulVec y)
      = x ⬝ᵥ y := by
  have h : ((A : Matrix.orthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)ᵀ *
      ((A : Matrix.orthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
    have := (A : Matrix.orthogonalGroup (Fin 3) ℝ).2.1
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose] using this
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, h, Matrix.vecMul_one]

/-- Non-vacuity: the three unit vectors along the coordinate axes span `ℝ³`. -/
theorem span_unitVectors :
    Submodule.span ℝ ((({Pi.single 0 1, Pi.single 1 1, Pi.single 2 1} :
      Finset (Fin 3 → ℝ))) : Set (Fin 3 → ℝ)) = ⊤ := by
  have hb := (Pi.basisFun ℝ (Fin 3)).span_eq
  rw [← hb]
  congr 1
  ext x
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
    Set.mem_singleton_iff, Set.mem_range, Pi.basisFun_apply]
  constructor
  · rintro (h | h | h) <;> subst h
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp

/-- An instance of the theorem: the point group of the "molecule" consisting of the three
unit vectors along the coordinate axes is finite. -/
example : Finite (pointGroup {Pi.single 0 1, Pi.single 1 1, Pi.single 2 1}) :=
  point_group_finite_O3 _ span_unitVectors

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

