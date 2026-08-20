import RequestProject.Schmidt

/-!
# Example: the Bell state

A concrete illustration of `QI.schmidt_decomposition`: the maximally entangled Bell state
on `ℂ^2 ⊗ ℂ^2` has Schmidt coefficients `1/√2, 1/√2`.
-/

open scoped BigOperators

namespace QI

/-- The Bell state `(|00⟩ + |11⟩)/√2` on `ℂ^2 ⊗ ℂ^2`. -/

lemma rho_apply_of_decomp {psi : Fin m × Fin n → ℂ} (D : SchmidtDecomp psi) (i i' : Fin m) :
    rho psi i i' = ∑ k, ((D.lam k : ℂ) ^ 2) * D.e k i * (starRingEnd ℂ) (D.e k i') := by
  have hf := D.f_orthonormal
  show (∑ j, psi (i, j) * (starRingEnd ℂ) (psi (i', j))) = _
  calc ∑ j, psi (i, j) * (starRingEnd ℂ) (psi (i', j))
      = ∑ j, (∑ k, (D.lam k : ℂ) * D.e k i * D.f k j) *
          (∑ l, (starRingEnd ℂ) ((D.lam l : ℂ) * D.e l i' * D.f l j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [D.eq_sum i j, D.eq_sum i' j, map_sum]
    _ = ∑ j, ∑ k, ∑ l, ((D.lam k : ℂ) * D.e k i * D.f k j) *
          (starRingEnd ℂ) ((D.lam l : ℂ) * D.e l i' * D.f l j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul_sum]
    _ = ∑ k, ∑ l, ∑ j, ((D.lam k : ℂ) * D.e k i * D.f k j) *
          (starRingEnd ℂ) ((D.lam l : ℂ) * D.e l i' * D.f l j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ k, ∑ l, ((D.lam k : ℂ) * (D.lam l : ℂ) * D.e k i * (starRingEnd ℂ) (D.e l i')) *
          (∑ j, (starRingEnd ℂ) (D.f l j) * D.f k j) := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [map_mul, Complex.conj_ofReal]
        ring
    _ = ∑ k, ((D.lam k : ℂ) ^ 2) * D.e k i * (starRingEnd ℂ) (D.e k i') := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => by rw [hf l k]]
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        ring

