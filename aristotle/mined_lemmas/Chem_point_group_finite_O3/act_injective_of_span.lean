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
