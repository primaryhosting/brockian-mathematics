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

lemma proj_eq_sum_rankOne {P : Matrix (Fin N) (Fin N) ℂ} (hP : IsProj P) :
    P = ∑ i ∈ Finset.univ.filter (fun i => hP.1.eigenvalues i = 1),
          rankOne (⇑(hP.1.eigenvectorBasis i)) := by
  classical
  rw [Finset.sum_filter]
  conv_lhs => rw [hermitian_eq_sum_rankOne hP.1]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : hP.1.eigenvalues i = 1
  · simp [h]
  · have h0 : hP.1.eigenvalues i = 0 := (proj_eigenvalues_eq_zero_or_one hP i).resolve_right h
    simp [h0]

/-! ## Gleason's theorem: reduction to regularity of the frame function -/

/-- If the frame function of a quantum measure is the quadratic form of a Hermitian matrix `T`,
then the measure is given by `P ↦ Re tr (T P)` on all projections. -/
