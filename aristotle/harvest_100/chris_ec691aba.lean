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

set_option maxHeartbeats 1000000

namespace Chem

open Matrix

/-- The orthogonal group `O(3)`, realized as the group of real `3 × 3` orthogonal
matrices (a matrix `A` is orthogonal iff `Aᵀ * A = 1`). -/
abbrev O3 : Type := Matrix.orthogonalGroup (Fin 3) ℝ

/-- The natural action of `O(3)` on `ℝ³` by matrix-vector multiplication. -/
def act (g : O3) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (g : Matrix (Fin 3) (Fin 3) ℝ).mulVec x

@[simp] theorem act_one (x : Fin 3 → ℝ) : act 1 x = x := by
  simp [act, Matrix.one_mulVec]

theorem act_mul (g h : O3) (x : Fin 3 → ℝ) : act (g * h) x = act g (act h x) := by
  simp [act, Matrix.mulVec_mulVec]

/-- Two orthogonal transformations that agree on a spanning set are equal. -/
theorem act_injective_of_span {s : Set (Fin 3 → ℝ)} (hspan : Submodule.span ℝ s = ⊤)
    {g h : O3} (hgh : ∀ x ∈ s, act g x = act h x) : g = h := by
  have hlin : Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) ℝ)
      = Matrix.toLin' (h : Matrix (Fin 3) (Fin 3) ℝ) := by
    refine LinearMap.ext_on hspan ?_
    intro x hx
    simpa [Matrix.toLin'_apply] using hgh x hx
  have : (g : Matrix (Fin 3) (Fin 3) ℝ) = (h : Matrix (Fin 3) (Fin 3) ℝ) :=
    Matrix.toLin'.injective hlin
  exact Subtype.ext this

/-- The point group of a (finite) molecular configuration `S ⊆ ℝ³`: the group of
orthogonal transformations of space that permute the atoms of the molecule. -/
def pointGroup (S : Finset (Fin 3 → ℝ)) : Subgroup O3 where
  carrier := {g | act g '' (S : Set (Fin 3 → ℝ)) = (S : Set (Fin 3 → ℝ))}
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq] at *
    have : act (g * h) '' (S : Set (Fin 3 → ℝ))
        = act g '' (act h '' (S : Set (Fin 3 → ℝ))) := by
      rw [← Set.image_comp]
      exact Set.image_congr' (fun x => act_mul g h x)
    rw [this, hh, hg]
  one_mem' := by
    simp [Set.mem_setOf_eq]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at *
    calc act g⁻¹ '' (S : Set (Fin 3 → ℝ))
        = act g⁻¹ '' (act g '' (S : Set (Fin 3 → ℝ))) := by rw [hg]
      _ = (S : Set (Fin 3 → ℝ)) := by
            rw [← Set.image_comp]
            refine (Set.image_congr' (g := id) ?_).trans (Set.image_id _)
            intro x
            simp [Function.comp, ← act_mul]

theorem mem_pointGroup_iff {S : Finset (Fin 3 → ℝ)} {g : O3} :
    g ∈ pointGroup S ↔ act g '' (S : Set (Fin 3 → ℝ)) = (S : Set (Fin 3 → ℝ)) :=
  Iff.rfl

theorem act_mem_of_mem_pointGroup {S : Finset (Fin 3 → ℝ)} {g : O3}
    (hg : g ∈ pointGroup S) {x : Fin 3 → ℝ} (hx : x ∈ S) : act g x ∈ S := by
  have : act g x ∈ act g '' (S : Set (Fin 3 → ℝ)) := ⟨x, hx, rfl⟩
  rw [mem_pointGroup_iff.mp hg] at this
  exact this

/-- **Every molecular point group is a finite subgroup of `O(3)`.**

A molecule is modelled by a finite set `S` of atomic positions in `ℝ³` which is not
contained in any plane through the origin (i.e. it spans `ℝ³`; this is the generic,
non-degenerate case, and one can always achieve it by adjoining the origin-centred
frame of the molecule). Its point group `pointGroup S` is by construction a subgroup
of the orthogonal group `O(3)`, and it is finite: every symmetry operation is
determined by the permutation it induces on the atoms. -/
theorem point_group_finite_O3 (S : Finset (Fin 3 → ℝ))
    (hspan : Submodule.span ℝ (S : Set (Fin 3 → ℝ)) = ⊤) :
    Finite (pointGroup S) := by
  haveI : Fintype (S : Set (Fin 3 → ℝ)) := FinsetCoe.fintype S
  refine Finite.of_injective
    (fun g : pointGroup S => fun x : (S : Set (Fin 3 → ℝ)) =>
      (⟨act (g : O3) (x : Fin 3 → ℝ),
        act_mem_of_mem_pointGroup g.2 x.2⟩ : (S : Set (Fin 3 → ℝ)))) ?_
  intro g h hgh
  apply Subtype.ext
  refine act_injective_of_span hspan ?_
  intro x hx
  have := congrArg (fun f => (f ⟨x, hx⟩ : Fin 3 → ℝ)) hgh
  simpa using this

/-- The spanning hypothesis in `point_group_finite_O3` is satisfiable: the three
unit vectors along the coordinate axes span `ℝ³`. -/
theorem span_axes_eq_top :
    Submodule.span ℝ
      ((Finset.univ.image (fun i : Fin 3 => (Pi.single i (1 : ℝ) : Fin 3 → ℝ)) :
        Finset (Fin 3 → ℝ)) : Set (Fin 3 → ℝ)) = ⊤ := by
  have hb := (Pi.basisFun ℝ (Fin 3)).span_eq
  rw [← hb]
  congr 1
  ext x
  simp [Pi.basisFun_apply, Set.range, eq_comm]

end Chem

