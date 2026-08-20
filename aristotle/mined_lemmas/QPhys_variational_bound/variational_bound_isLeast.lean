/-
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped InnerProductSpace

namespace QPhys

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- `⟨ψ|ψ⟩` is real and equals `‖ψ‖ ^ 2`. -/

theorem variational_bound_isLeast [Nonempty (Fin n)] (b : OrthonormalBasis (Fin n) ℂ V)
    (H : V →ₗ[ℂ] V) (E : Fin n → ℝ) (hH : ∀ i, H (b i) = (E i : ℂ) • b i) :
    IsLeast {r : ℝ | ∃ ψ : V, ψ ≠ 0 ∧ r = (inner ℂ ψ (H ψ)).re / (inner ℂ ψ ψ).re}
      (Finset.univ.inf' Finset.univ_nonempty E) := by
  constructor
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Fin n)) E
    refine ⟨b i, ?_, ?_⟩
    · simpa using b.orthonormal.ne_zero i
    · rw [rayleigh_quotient_eigenvector b H E hH i, hi]
  · rintro r ⟨ψ, hψ, rfl⟩
    exact variational_bound b H E _ hH (fun i => Finset.inf'_le E (Finset.mem_univ i)) ψ hψ

end QPhys

