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

theorem span_octahedralAxes :
    Submodule.span ℝ ((octahedralAxes : Finset (Fin 3 → ℝ)) : Set (Fin 3 → ℝ)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun ℝ (Fin 3)).span_eq, Submodule.span_le]
  rintro x hx
  simp only [Set.mem_range, Pi.basisFun_apply] at hx
  obtain ⟨i, rfl⟩ := hx
  apply Submodule.subset_span
  fin_cases i <;> simp [octahedralAxes]

/-- The inversion `-1` is an orthogonal transformation. -/
