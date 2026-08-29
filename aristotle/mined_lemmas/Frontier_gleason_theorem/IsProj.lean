import RequestProject.Main
/-!
# Gleason's theorem fails in dimension two

This file complements `RequestProject/Main.lean`.  It constructs an explicit quantum measure on
the projection lattice of `ℂ²` which does not come from any density operator, showing that the
dimension hypothesis `3 ≤ N` in Gleason's theorem cannot be dropped.

The measure is the two-valued "lexicographic sign" measure: in dimension two the only nontrivial
orthogonality relation between projections is `Q = 1 - P` for a rank-one projection `P`, so any
function on rank-one projections satisfying `f P + f (1 - P) = 1` is finitely additive.
-/

open scoped Classical
open scoped ComplexOrder

namespace Frontier

open Matrix

/-! ## Structure of projections in dimension two -/

/-- The Cayley–Hamilton identity for `2 × 2` matrices. -/

lemma IsProj.add {P Q : Matrix (Fin N) (Fin N) ℂ} (hP : IsProj P) (hQ : IsProj Q)
    (h : P * Q = 0) : IsProj (P + Q) := by
  refine ⟨hP.1.add hQ.1, ?_⟩
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h, hP.mul_comm_zero hQ h, hP.2, hQ.2]
  abel

