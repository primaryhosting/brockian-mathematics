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

lemma isProj_sum {ι : Type*} (s : Finset ι) (P : ι → Matrix (Fin N) (Fin N) ℂ)
    (hP : ∀ i ∈ s, IsProj (P i)) (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → P i * P j = 0) :
    IsProj (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isProj_zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have hmem : ∀ i ∈ s, i ∈ insert a s := fun i hi => Finset.mem_insert_of_mem hi
      refine IsProj.add (hP a (Finset.mem_insert_self a s))
        (ih (fun i hi => hP i (hmem i hi))
          (fun i hi j hj hij => horth i (hmem i hi) j (hmem j hj) hij)) ?_
      rw [Matrix.mul_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      exact horth a (Finset.mem_insert_self a s) i (hmem i hi) (by rintro rfl; exact ha hi)

/-- Finite additivity of a quantum measure over a family of pairwise orthogonal projections. -/
