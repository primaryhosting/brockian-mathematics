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

lemma qform_nonpos_of_mem_eigenSpan {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) {x : m → 𝕜}
    (hx : x ∈ eigenSpan hQ (fun i => hQ.eigenvalues i ≤ 0)) : qform Q x ≤ 0 := by
  obtain ⟨c, hc, rfl⟩ := exists_coeff_of_mem_eigenSpan hQ _ hx
  rw [qform_sum_evec]
  refine Finset.sum_nonpos fun i _ => ?_
  by_cases hi : hQ.eigenvalues i ≤ 0
  · exact mul_nonpos_of_nonpos_of_nonneg hi (by positivity)
  · simp [hc i hi]

