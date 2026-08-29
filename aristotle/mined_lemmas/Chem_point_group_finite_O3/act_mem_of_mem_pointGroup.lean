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
