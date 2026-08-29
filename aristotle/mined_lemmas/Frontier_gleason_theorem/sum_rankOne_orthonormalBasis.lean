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

lemma sum_rankOne_orthonormalBasis (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    ∑ i, rankOne (⇑(b i)) = (1 : Matrix (Fin N) (Fin N) ℂ) := by
  classical
  set U : Matrix (Fin N) (Fin N) ℂ :=
    (EuclideanSpace.basisFun (Fin N) ℂ).toBasis.toMatrix b.toBasis with hUdef
  have hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ :=
    (EuclideanSpace.basisFun (Fin N) ℂ).toMatrix_orthonormalBasis_mem_unitary b
  have hUU : U * star U = 1 := by
    simpa using (Matrix.mem_unitaryGroup_iff).mp hU
  have hentry : ∀ i j : Fin N, U i j = (b j : EuclideanSpace ℂ (Fin N)) i := fun _ _ => rfl
  ext j k
  have hjk := congrFun (congrFun hUU j) k
  rw [Matrix.mul_apply] at hjk
  simp only [Matrix.sum_apply, rankOne, Matrix.vecMulVec_apply, Pi.star_apply]
  rw [← hjk]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [hentry, Matrix.star_apply]

/-- **Frame function property.** For any quantum measure and any orthonormal basis, the values
of the measure on the rank-one projections onto the basis vectors sum to one. -/
