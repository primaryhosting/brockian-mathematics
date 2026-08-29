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

set_option grind.warning false

namespace Chem

/-- The orthogonal group `O(3)`, realized as the group of real `3 × 3` orthogonal matrices. -/
abbrev O3 : Type := ↥(Matrix.orthogonalGroup (Fin 3) ℝ)

/-- The natural action of `O(3)` on Euclidean 3-space. -/
def act (g : O3) (x : Fin 3 → ℝ) : Fin 3 → ℝ := g.1.mulVec x

@[simp] lemma act_one (x : Fin 3 → ℝ) : act 1 x = x := Matrix.one_mulVec x

lemma act_mul (g h : O3) (x : Fin 3 → ℝ) : act (g * h) x = act g (act h x) :=
  (Matrix.mulVec_mulVec x g.1 h.1).symm

@[simp] lemma act_inv_act (g : O3) (x : Fin 3 → ℝ) : act g⁻¹ (act g x) = x := by
  rw [← act_mul, inv_mul_cancel, act_one]

/-- A molecule: a finite set of nuclear positions in Euclidean 3-space, each atom carrying a
species label (e.g. its atomic number). -/
structure Molecule where
  /-- The set of nuclear positions. -/
  atoms : Set (Fin 3 → ℝ)
  /-- A molecule has finitely many atoms. -/
  atoms_finite : atoms.Finite
  /-- The chemical species (say, atomic number) sitting at a given position. -/
  species : (Fin 3 → ℝ) → ℕ

/-- The molecular point group of `M`: the subgroup of `O(3)` consisting of those orthogonal
transformations which map the nuclear framework onto itself, preserving atomic species. -/
def pointGroup (M : Molecule) : Subgroup O3 where
  carrier := {g | act g '' M.atoms = M.atoms ∧
    ∀ x ∈ M.atoms, M.species (act g x) = M.species x}
  one_mem' := by
    refine ⟨?_, ?_⟩
    · have h1 : act 1 = id := funext act_one
      rw [h1, Set.image_id]
    · intro x _
      rw [act_one]
  mul_mem' := by
    rintro g h ⟨hg, hgs⟩ ⟨hh, hhs⟩
    constructor
    · have hcomp : act (g * h) '' M.atoms = act g '' (act h '' M.atoms) := by
        rw [Set.image_image]
        exact Set.image_congr' (fun x => act_mul g h x)
      rw [hcomp, hh, hg]
    · intro x hx
      rw [act_mul, hgs _ (by rw [← hh]; exact ⟨x, hx, rfl⟩), hhs x hx]
  inv_mem' := by
    rintro g ⟨hg, hgs⟩
    constructor
    · conv_lhs => rw [← hg]
      rw [Set.image_image]
      have h1 : (fun x => act g⁻¹ (act g x)) = id := funext (act_inv_act g)
      rw [h1, Set.image_id]
    · intro y hy
      rw [← hg] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [act_inv_act, hgs x hx]

/-- **Every molecular point group is a finite subgroup of `O(3)`.**

By construction `Chem.pointGroup M` is a subgroup of `O(3)`; the content here is finiteness.
The hypothesis that the nuclei span `ℝ³` is genuinely needed: a linear molecule (whose nuclei
span only a line) has the infinite point group `C∞v` or `D∞h`. -/
theorem point_group_finite_O3 (M : Molecule) (hspan : Submodule.span ℝ M.atoms = ⊤) :
    Finite ↥(pointGroup M) := by
  haveI : Finite ↥M.atoms := M.atoms_finite.to_subtype
  refine Finite.of_injective
    (fun g : ↥(pointGroup M) => (fun x : ↥M.atoms => (⟨act g.1 x.1, ?_⟩ : ↥M.atoms))) ?_
  · have hx : act g.1 x.1 ∈ act g.1 '' M.atoms := ⟨x.1, x.2, rfl⟩
    rwa [g.2.1] at hx
  · intro g h hgh
    have hEq : ∀ x ∈ M.atoms, act g.1 x = act h.1 x := by
      intro x hx
      have := congrArg (fun F => (F ⟨x, hx⟩ : Fin 3 → ℝ)) hgh
      simpa using this
    have : Matrix.toLin' g.1.1 = Matrix.toLin' h.1.1 :=
      LinearMap.ext_on hspan (by
        intro x hx
        simpa [Matrix.toLin'_apply, act] using hEq x hx)
    have hm : (g.1 : Matrix (Fin 3) (Fin 3) ℝ) = (h.1 : Matrix (Fin 3) (Fin 3) ℝ) :=
      Matrix.toLin'.injective this
    exact Subtype.ext (Subtype.ext hm)

end Chem

