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

theorem inversion_mem_pointGroup_octahedralAxes :
    (⟨-1, neg_one_mem_O3⟩ : ↥O3) ∈ pointGroup octahedralAxes := by
  intro v
  have hv : ((⟨-1, neg_one_mem_O3⟩ : ↥O3) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v = -v := by
    simp [Matrix.neg_mulVec]
  rw [hv]
  simp only [octahedralAxes, Finset.mem_insert, Finset.mem_singleton, neg_eq_iff_eq_neg, neg_neg]
  tauto

/-- The point group of the octahedral positions is a nontrivial finite subgroup of `O(3)`. -/
