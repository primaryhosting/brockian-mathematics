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

lemma IsQuantumMeasure.sum {μ : Matrix (Fin N) (Fin N) ℂ → ℝ} (hμ : IsQuantumMeasure μ)
    {ι : Type*} (s : Finset ι) (P : ι → Matrix (Fin N) (Fin N) ℂ)
    (hP : ∀ i ∈ s, IsProj (P i)) (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → P i * P j = 0) :
    μ (∑ i ∈ s, P i) = ∑ i ∈ s, μ (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hμ.map_zero
  | insert a s ha ih =>
      have hmem : ∀ i ∈ s, i ∈ insert a s := fun i hi => Finset.mem_insert_of_mem hi
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih (fun i hi => hP i (hmem i hi))
        (fun i hi j hj hij => horth i (hmem i hi) j (hmem j hj) hij)]
      refine hμ.additive _ _ (hP a (Finset.mem_insert_self a s))
        (isProj_sum s P (fun i hi => hP i (hmem i hi))
          (fun i hi j hj hij => horth i (hmem i hi) j (hmem j hj) hij)) ?_
      rw [Matrix.mul_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      exact horth a (Finset.mem_insert_self a s) i (hmem i hi) (by rintro rfl; exact ha hi)

/-! ## Spectral decomposition into rank-one projections -/

/-- The vectors of an orthonormal basis of `ℂ^N` are orthonormal for the dot product. -/
