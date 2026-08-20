import RequestProject.Schmidt

/-!
# Example: the Bell state

A concrete illustration of `QI.schmidt_decomposition`: the maximally entangled Bell state
on `ℂ^2 ⊗ ℂ^2` has Schmidt coefficients `1/√2, 1/√2`.
-/

open scoped BigOperators

namespace QI

/-- The Bell state `(|00⟩ + |11⟩)/√2` on `ℂ^2 ⊗ ℂ^2`. -/

lemma pow_rho_apply {psi : Fin m × Fin n → ℂ} (D : SchmidtDecomp psi) :
    ∀ p : ℕ, ∀ i i' : Fin m,
      ((rho psi) ^ (p + 1)) i i' =
        ∑ k, ((D.lam k : ℂ) ^ (2 * (p + 1))) * D.e k i * (starRingEnd ℂ) (D.e k i') := by
  have he := D.e_orthonormal
  intro p
  induction p with
  | zero =>
      intro i i'
      rw [pow_one]
      simpa using rho_apply_of_decomp D i i'
  | succ q ih =>
      intro i i'
      rw [pow_succ, Matrix.mul_apply]
      calc ∑ x, ((rho psi) ^ (q + 1)) i x * (rho psi) x i'
          = ∑ x, (∑ k, ((D.lam k : ℂ) ^ (2 * (q + 1))) * D.e k i * (starRingEnd ℂ) (D.e k x)) *
              (∑ l, ((D.lam l : ℂ) ^ 2) * D.e l x * (starRingEnd ℂ) (D.e l i')) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [ih i x, rho_apply_of_decomp D x i']
        _ = ∑ x, ∑ k, ∑ l, (((D.lam k : ℂ) ^ (2 * (q + 1))) * D.e k i * (starRingEnd ℂ) (D.e k x)) *
              (((D.lam l : ℂ) ^ 2) * D.e l x * (starRingEnd ℂ) (D.e l i')) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.sum_mul_sum]
        _ = ∑ k, ∑ l, ∑ x, (((D.lam k : ℂ) ^ (2 * (q + 1))) * D.e k i * (starRingEnd ℂ) (D.e k x)) *
              (((D.lam l : ℂ) ^ 2) * D.e l x * (starRingEnd ℂ) (D.e l i')) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.sum_comm]
        _ = ∑ k, ∑ l, (((D.lam k : ℂ) ^ (2 * (q + 1))) * ((D.lam l : ℂ) ^ 2) * D.e k i *
              (starRingEnd ℂ) (D.e l i')) * (∑ x, (starRingEnd ℂ) (D.e k x) * D.e l x) := by
            refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => ?_
            ring
        _ = ∑ k, ((D.lam k : ℂ) ^ (2 * (q + 1 + 1))) * D.e k i * (starRingEnd ℂ) (D.e k i') := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => by rw [he k l]]
            simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
            ring

