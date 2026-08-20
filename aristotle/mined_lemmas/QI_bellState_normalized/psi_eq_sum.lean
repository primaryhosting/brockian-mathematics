import RequestProject.Schmidt

/-!
# Example: the Bell state

A concrete illustration of `QI.schmidt_decomposition`: the maximally entangled Bell state
on `ℂ^2 ⊗ ℂ^2` has Schmidt coefficients `1/√2, 1/√2`.
-/

open scoped BigOperators

namespace QI

/-- The Bell state `(|00⟩ + |11⟩)/√2` on `ℂ^2 ⊗ ℂ^2`. -/

lemma psi_eq_sum (i : Fin m) (j : Fin n) :
    psi (i, j) = ∑ k, eigVec psi k i * wvec psi k j := by
  symm
  calc ∑ k, eigVec psi k i * wvec psi k j
      = ∑ k, ∑ i', eigVec psi k i * ((starRingEnd ℂ) (eigVec psi k i') * psi (i', j)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [wvec, Finset.mul_sum]
    _ = ∑ i', ∑ k, eigVec psi k i * ((starRingEnd ℂ) (eigVec psi k i') * psi (i', j)) := by
        rw [Finset.sum_comm]
    _ = ∑ i', (∑ k, eigVec psi k i * (starRingEnd ℂ) (eigVec psi k i')) * psi (i', j) := by
        refine Finset.sum_congr rfl fun i' _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = psi (i, j) := by
        rw [Finset.sum_congr rfl fun i' (_ : i' ∈ Finset.univ) => by
          rw [eigVec_complete psi i i']]
        simp

end Existence

