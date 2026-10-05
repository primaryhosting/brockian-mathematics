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

