import RequestProject.Schmidt

/-!
# Example: the Bell state

A concrete illustration of `QI.schmidt_decomposition`: the maximally entangled Bell state
on `ℂ^2 ⊗ ℂ^2` has Schmidt coefficients `1/√2, 1/√2`.
-/

open scoped BigOperators

namespace QI

/-- The Bell state `(|00⟩ + |11⟩)/√2` on `ℂ^2 ⊗ ℂ^2`. -/

lemma wvec_eq_zero (k : Fin m) (hk : eigMu psi k = 0) : wvec psi k = 0 := by
  have h := wvec_inner psi k k
  rw [if_pos rfl, hk] at h
  have h' : ∑ j, (starRingEnd ℂ) (wvec psi k j) * wvec psi k j = 0 := by simpa using h
  have h2 : ((∑ j, ‖wvec psi k j‖ ^ 2 : ℝ) : ℂ) = 0 := by
    rw [← h']
    push_cast
    refine (Finset.sum_congr rfl fun j _ => ?_).symm
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have h3 : ∑ j, ‖wvec psi k j‖ ^ 2 = 0 := by exact_mod_cast h2
  have h4 : ∀ j ∈ (Finset.univ : Finset (Fin n)), ‖wvec psi k j‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).1 h3
  funext j
  have := h4 j (Finset.mem_univ j)
  have : ‖wvec psi k j‖ = 0 := by nlinarith [norm_nonneg (wvec psi k j)]
  simpa using this

