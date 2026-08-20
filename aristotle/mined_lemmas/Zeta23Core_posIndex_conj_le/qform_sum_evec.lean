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

lemma qform_sum_evec {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) (c : m → 𝕜) :
    qform Q (∑ i, c i • evec hQ i) = ∑ i, hQ.eigenvalues i * ‖c i‖ ^ 2 := by
  have h1 : Q *ᵥ (∑ i, c i • evec hQ i) = ∑ i, (c i * (hQ.eigenvalues i : 𝕜)) • evec hQ i := by
    rw [mulVec_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mulVec_smul, mulVec_evec, RCLike.real_smul_eq_coe_smul (K := 𝕜), smul_smul]
  rw [qform, h1, star_sum, sum_dotProduct]
  have key : ∀ i : m, (star (c i • evec hQ i)) ⬝ᵥ (∑ j, (c j * (hQ.eigenvalues j : 𝕜)) • evec hQ j)
      = (starRingEnd 𝕜) (c i) * (c i * (hQ.eigenvalues i : 𝕜)) := by
    intro i
    rw [dotProduct_sum, Finset.sum_eq_single i]
    · simp only [star_smul, smul_dotProduct, dotProduct_smul, evec_dotProduct, smul_eq_mul,
        if_pos, RCLike.star_def, mul_one]
      ring
    · intro j _ hj
      simp [star_smul, smul_dotProduct, dotProduct_smul, evec_dotProduct, smul_eq_mul,
        Ne.symm hj]
    · simp
  simp only [key]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : (starRingEnd 𝕜) (c i) * (c i * (hQ.eigenvalues i : 𝕜))
      = ((‖c i‖ ^ 2 * hQ.eigenvalues i : ℝ) : 𝕜) := by
    rw [← mul_assoc, RCLike.conj_mul]
    push_cast
    ring
  rw [h2, RCLike.ofReal_re]
  ring

/-- The span of the eigenvectors whose index satisfies `p`. -/
