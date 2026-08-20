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

theorem exists_posDef_subspace {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) :
    ∃ S : Submodule 𝕜 (m → 𝕜), finrank 𝕜 S = posIndex Q ∧ ∀ x ∈ S, x ≠ 0 → 0 < qform Q x := by
  refine ⟨eigenSpan hQ (fun i => 0 < hQ.eigenvalues i), ?_, fun x hx hx0 =>
    qform_pos_of_mem_eigenSpan hQ hx hx0⟩
  rw [finrank_eigenSpan, posIndex_eq_card hQ]

omit [DecidableEq m] in
