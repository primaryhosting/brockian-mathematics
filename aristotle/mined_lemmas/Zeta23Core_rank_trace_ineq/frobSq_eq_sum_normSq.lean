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

lemma frobSq_eq_sum_normSq {ι : Type*} [Fintype ι] (M : Matrix n n 𝕜)
    (f : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 n)) :
    frobSq M = ∑ i, ‖Matrix.toEuclideanLin M (f i)‖ ^ 2 := by
  unfold frobSq
  rw [trace_eq_sum_diag _ f, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : Matrix.toEuclideanLin (Mᴴ * M)
      = (LinearMap.adjoint (Matrix.toEuclideanLin M)) ∘ₗ (Matrix.toEuclideanLin M) := by
    rw [Matrix.toLpLin_mul 2 2 2, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rw [h]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.adjoint_inner_right]
  rw [inner_self_eq_norm_sq_to_K]
  simp

/-- In any orthonormal basis, the sum of the squares of the real parts of the diagonal entries
is at most the squared Frobenius norm. -/
