import Mathlib

/-!
# Molecular point groups are finite subgroups of O(3)

A molecule is modelled by the set `S ⊆ ℝ³` of its nuclear positions, placed so that the
centre of mass sits at the origin.  Its *point group* is the group of all orthogonal
transformations of `ℝ³` mapping the molecule onto itself; by construction this is a
subgroup of `O(3)` (here realised as the group `Matrix.orthogonalGroup (Fin 3) ℝ` of real
orthogonal `3 × 3` matrices acting on `Fin 3 → ℝ` by `mulVec`).

The main theorem `Chem.point_group_finite_O3` shows that this subgroup is finite for every
molecule with finitely many atoms whose positions span `ℝ³`.  The spanning hypothesis
cannot be dropped: a linear molecule such as CO₂ has the infinite point group `D∞h`
(all rotations about the molecular axis are symmetries).
-/

namespace Chem

open Matrix

/-- The orthogonal group `O(3)`, realised as real orthogonal `3 × 3` matrices. -/
abbrev O3 : Submonoid (Matrix (Fin 3) (Fin 3) ℝ) := Matrix.orthogonalGroup (Fin 3) ℝ

/-- The natural action of `O(3)` on `ℝ³`. -/

lemma rotZ_mem (θ : ℝ) : rotZ θ ∈ pointGroup diatomic := by
  show act (rotZ θ) '' diatomic = diatomic
  have h1 : act (rotZ θ) ![0, 0, 1] = ![0, 0, 1] := by
    funext i; fin_cases i <;> simp [act, rotZ, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have h2 : act (rotZ θ) ![0, 0, -1] = ![0, 0, -1] := by
    funext i; fin_cases i <;> simp [act, rotZ, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  simp [diatomic, Set.image_insert_eq, h1, h2]

/-- The point group of a linear molecule is infinite, so the spanning hypothesis in
`Chem.point_group_finite_O3` cannot be dropped. -/
