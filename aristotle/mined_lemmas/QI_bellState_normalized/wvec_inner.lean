import RequestProject.Schmidt

/-!
# Example: the Bell state

A concrete illustration of `QI.schmidt_decomposition`: the maximally entangled Bell state
on `ℂ^2 ⊗ ℂ^2` has Schmidt coefficients `1/√2, 1/√2`.
-/

open scoped BigOperators

namespace QI

/-- The Bell state `(|00⟩ + |11⟩)/√2` on `ℂ^2 ⊗ ℂ^2`. -/

lemma wvec_inner (k l : Fin m) :
    ∑ j, (starRingEnd ℂ) (wvec psi k j) * wvec psi l j =
      if k = l then (eigMu psi k : ℂ) else 0 := by
  calc ∑ j, (starRingEnd ℂ) (wvec psi k j) * wvec psi l j
      = ∑ j, (∑ i, eigVec psi k i * (starRingEnd ℂ) (psi (i, j))) *
          (∑ i', (starRingEnd ℂ) (eigVec psi l i') * psi (i', j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [wvec, map_sum, map_mul, Complex.conj_conj]
    _ = ∑ j, ∑ i, ∑ i', (eigVec psi k i * (starRingEnd ℂ) (psi (i, j))) *
          ((starRingEnd ℂ) (eigVec psi l i') * psi (i', j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul_sum]
    _ = ∑ i, ∑ i', ∑ j, (eigVec psi k i * (starRingEnd ℂ) (psi (i, j))) *
          ((starRingEnd ℂ) (eigVec psi l i') * psi (i', j)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ i', ∑ i, ∑ j, (eigVec psi k i * (starRingEnd ℂ) (psi (i, j))) *
          ((starRingEnd ℂ) (eigVec psi l i') * psi (i', j)) := by
        rw [Finset.sum_comm]
    _ = ∑ i', (starRingEnd ℂ) (eigVec psi l i') * (∑ i, rho psi i' i * eigVec psi k i) := by
        refine Finset.sum_congr rfl fun i' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        show _ = (starRingEnd ℂ) (eigVec psi l i') *
          ((∑ j, psi (i', j) * (starRingEnd ℂ) (psi (i, j))) * eigVec psi k i)
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = if k = l then (eigMu psi k : ℂ) else 0 := by
        have : ∀ i', (starRingEnd ℂ) (eigVec psi l i') * (∑ i, rho psi i' i * eigVec psi k i)
            = (eigMu psi k : ℂ) * ((starRingEnd ℂ) (eigVec psi l i') * eigVec psi k i') := by
          intro i'
          rw [rho_mulVec_eigVec]
          ring
        rw [Finset.sum_congr rfl fun i' (_ : i' ∈ Finset.univ) => this i', ← Finset.mul_sum,
          eigVec_orthonormal psi l k]
        by_cases h : k = l
        · simp [h]
        · simp [h, Ne.symm h]

