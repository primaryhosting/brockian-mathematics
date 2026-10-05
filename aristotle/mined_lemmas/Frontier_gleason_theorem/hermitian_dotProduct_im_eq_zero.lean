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

lemma hermitian_dotProduct_im_eq_zero {T : Matrix (Fin N) (Fin N) ℂ} (hT : T.IsHermitian)
    (v : Fin N → ℂ) : (star v ⬝ᵥ T *ᵥ v).im = 0 := by
  have h : star (star v ⬝ᵥ T *ᵥ v) = star v ⬝ᵥ T *ᵥ v := by
    simp only [dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← hT.apply i j]
    simp only [star_star]
    ring
  exact Complex.conj_eq_iff_im.mp h

/-- The trace of a Hermitian matrix is real. -/
