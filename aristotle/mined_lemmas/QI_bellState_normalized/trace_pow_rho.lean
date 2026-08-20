import RequestProject.Schmidt

/-!
# Example: the Bell state

A concrete illustration of `QI.schmidt_decomposition`: the maximally entangled Bell state
on `ℂ^2 ⊗ ℂ^2` has Schmidt coefficients `1/√2, 1/√2`.
-/

open scoped BigOperators

namespace QI

/-- The Bell state `(|00⟩ + |11⟩)/√2` on `ℂ^2 ⊗ ℂ^2`. -/

lemma trace_pow_rho {psi : Fin m × Fin n → ℂ} (D : SchmidtDecomp psi) (p : ℕ) :
    ((rho psi) ^ (p + 1)).trace = ∑ k, ((D.lam k : ℂ) ^ (2 * (p + 1))) := by
  have he := D.e_orthonormal
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  calc ∑ i, ((rho psi) ^ (p + 1)) i i
      = ∑ i, ∑ k, ((D.lam k : ℂ) ^ (2 * (p + 1))) * D.e k i * (starRingEnd ℂ) (D.e k i) := by
        exact Finset.sum_congr rfl fun i _ => pow_rho_apply D p i i
    _ = ∑ k, ((D.lam k : ℂ) ^ (2 * (p + 1))) * (∑ i, (starRingEnd ℂ) (D.e k i) * D.e k i) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ k, ((D.lam k : ℂ) ^ (2 * (p + 1))) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [he k k]
        simp

/-- The power sums of the squared Schmidt coefficients are determined by `psi`. -/
