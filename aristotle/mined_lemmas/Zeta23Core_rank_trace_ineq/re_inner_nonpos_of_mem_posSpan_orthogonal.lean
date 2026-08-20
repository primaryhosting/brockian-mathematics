/-
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring; the header above is
-- reproduced verbatim as a module docstring immediately after the import.)
import Mathlib

/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Core

open Matrix RCLike Finset

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The squared Frobenius norm of a matrix, `‖M‖_F² = Re tr(Mᴴ M)`. -/

lemma re_inner_nonpos_of_mem_posSpan_orthogonal {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian)
    {x : EuclideanSpace 𝕜 n} (hx : x ∈ (posSpan hQ)ᗮ) :
    RCLike.re (inner 𝕜 x (Matrix.toEuclideanLin Q x)) ≤ 0 := by
  set v := hQ.eigenvectorBasis with hv
  have hev : ∀ i, Matrix.toEuclideanLin Q (v i) = (hQ.eigenvalues i : 𝕜) • (v i) := by
    intro i
    apply WithLp.ofLp_injective (p := 2)
    simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul, hv]
    rw [← RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    exact hQ.mulVec_eigenvectorBasis i
  have hzero : ∀ i, 0 < hQ.eigenvalues i → inner 𝕜 (v i) x = 0 := by
    intro i hi
    refine (Submodule.mem_orthogonal _ _).1 hx (v i) ?_
    exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  have key : inner 𝕜 x (Matrix.toEuclideanLin Q x)
      = ∑ i, ((hQ.eigenvalues i * ‖inner 𝕜 (v i) x‖ ^ 2 : ℝ) : 𝕜) := by
    rw [← v.sum_inner_mul_inner x (Matrix.toEuclideanLin Q x)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsym : (Matrix.toEuclideanLin Q).IsSymmetric := Matrix.isHermitian_iff_isSymmetric.1 hQ
    rw [← hsym (v i) x, hev i, inner_smul_left, RCLike.conj_ofReal, ← inner_conj_symm x (v i)]
    rw [show (starRingEnd 𝕜) (inner 𝕜 (v i) x) * ((hQ.eigenvalues i : 𝕜) * inner 𝕜 (v i) x)
        = (hQ.eigenvalues i : 𝕜) * (inner 𝕜 (v i) x * (starRingEnd 𝕜) (inner 𝕜 (v i) x)) from by
      ring, RCLike.mul_conj]
    push_cast
    ring
  rw [key, map_sum]
  refine Finset.sum_nonpos fun i _ => ?_
  rw [RCLike.ofReal_re]
  rcases lt_or_ge 0 (hQ.eigenvalues i) with h | h
  · rw [hzero i h]; simp
  · exact mul_nonpos_of_nonpos_of_nonneg h (by positivity)

/-- A subfamily of an orthonormal basis contained in a subspace has at most `finrank` many
members. -/
