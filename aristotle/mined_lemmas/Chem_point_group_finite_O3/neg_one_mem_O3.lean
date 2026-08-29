/-
# Point Group Finite O 3
Category: Chemistry
Target: Chem.point_group_finite_O3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix

/-- The orthogonal group `O(3)`, realized as the group of `3 × 3` real orthogonal matrices. -/
abbrev O3 : Submonoid (Matrix (Fin 3) (Fin 3) ℝ) := Matrix.orthogonalGroup (Fin 3) ℝ

/-- The **molecular point group** of a molecule whose nuclei occupy the finite set of
positions `S ⊆ ℝ³` (with the centre of mass at the origin): the subgroup of `O(3)`
consisting of those orthogonal transformations that map the set of nuclear positions
onto itself. -/

theorem neg_one_mem_O3 : (-1 : Matrix (Fin 3) (Fin 3) ℝ) ∈ O3 := by
  rw [Matrix.mem_orthogonalGroup_iff]
  simp

/-- The inversion centre belongs to the point group of the octahedral positions, so this
point group is nontrivial (in particular the finiteness statement is not vacuous). -/
