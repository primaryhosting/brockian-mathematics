import Mathlib

/-!
# Pos Index Conj Le
Category: Brockian Corpus
Target: Zeta23Core.posIndex_conj_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Module Submodule

namespace Zeta23Core

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [DecidableEq m] [Fintype d]

/-- The (real) quadratic form `x ↦ xᴴ Q x` associated with a square matrix `Q`. -/

lemma qform_pos_of_mem_eigenSpan {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) {x : m → 𝕜}
    (hx : x ∈ eigenSpan hQ (fun i => 0 < hQ.eigenvalues i)) (hx0 : x ≠ 0) : 0 < qform Q x := by
  obtain ⟨c, hc, rfl⟩ := exists_coeff_of_mem_eigenSpan hQ _ hx
  rw [qform_sum_evec]
  have hne : ∃ i, c i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 (by simp [h])
  obtain ⟨i₀, hi₀⟩ := hne
  have hp : 0 < hQ.eigenvalues i₀ := by
    by_contra h
    exact hi₀ (hc i₀ h)
  refine Finset.sum_pos' (fun i _ => ?_) ⟨i₀, Finset.mem_univ _, ?_⟩
  · by_cases hi : 0 < hQ.eigenvalues i
    · positivity
    · simp [hc i hi]
  · have : 0 < ‖c i₀‖ ^ 2 := by positivity
    exact mul_pos hp this

