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

lemma hermitian_eq_sum_rankOne {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) :
    A = ∑ i, (hA.eigenvalues i : ℂ) • rankOne (⇑(hA.eigenvectorBasis i)) := by
  ext j k
  conv_lhs => rw [hA.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    rankOne, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, mul_comm, mul_assoc]

/-- The eigenvalues of an orthogonal projection are `0` or `1`. -/
