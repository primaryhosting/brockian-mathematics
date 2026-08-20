import RequestProject.Schmidt

/-!
# Example: the Bell state

A concrete illustration of `QI.schmidt_decomposition`: the maximally entangled Bell state
on `ℂ^2 ⊗ ℂ^2` has Schmidt coefficients `1/√2, 1/√2`.
-/

open scoped BigOperators

namespace QI

/-- The Bell state `(|00⟩ + |11⟩)/√2` on `ℂ^2 ⊗ ℂ^2`. -/

lemma sum_lam_pow {psi : Fin m × Fin n → ℂ} (D D' : SchmidtDecomp psi) (p : ℕ) (hp : 1 ≤ p) :
    ∑ k, (D.lam k ^ 2) ^ p = ∑ k, (D'.lam k ^ 2) ^ p := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have cast_sum : ∀ E : SchmidtDecomp psi,
      ((∑ k, (E.lam k ^ 2) ^ (q + 1) : ℝ) : ℂ) = ∑ k, ((E.lam k : ℂ) ^ (2 * (q + 1))) := by
    intro E
    push_cast
    exact Finset.sum_congr rfl fun k _ => by rw [← pow_mul]
  have : ((∑ k, (D.lam k ^ 2) ^ (q + 1) : ℝ) : ℂ) = ((∑ k, (D'.lam k ^ 2) ^ (q + 1) : ℝ) : ℂ) := by
    rw [cast_sum D, cast_sum D', ← trace_pow_rho D q, ← trace_pow_rho D' q]
  exact_mod_cast this

/-! ### Existence -/

section Existence

variable (psi : Fin m × Fin n → ℂ)

/-- Eigenvalues of the reduced density matrix. -/
