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

lemma two_dim_cayley (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

/-- A `2 × 2` orthogonal projection is `0`, `1`, or has trace one (i.e. has rank one). -/
