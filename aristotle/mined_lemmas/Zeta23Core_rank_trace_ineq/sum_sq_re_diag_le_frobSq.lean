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

lemma sum_sq_re_diag_le_frobSq {ι : Type*} [Fintype ι] (M : Matrix n n 𝕜)
    (f : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 n)) :
    ∑ i, (RCLike.re (inner 𝕜 (f i) (Matrix.toEuclideanLin M (f i)))) ^ 2 ≤ frobSq M := by
  rw [frobSq_eq_sum_normSq M f]
  refine Finset.sum_le_sum fun i _ => ?_
  set L := Matrix.toEuclideanLin M
  have h1 : |RCLike.re (inner 𝕜 (f i) (L (f i)))| ≤ ‖(inner 𝕜 (f i) (L (f i)) : 𝕜)‖ :=
    RCLike.abs_re_le_norm _
  have h2 : ‖(inner 𝕜 (f i) (L (f i)) : 𝕜)‖ ≤ ‖f i‖ * ‖L (f i)‖ := norm_inner_le_norm _ _
  have h3 : ‖f i‖ = 1 := f.orthonormal.1 i
  rw [h3, one_mul] at h2
  nlinarith [h1.trans h2, sq_abs (RCLike.re (inner 𝕜 (f i) (L (f i)))),
    abs_nonneg (RCLike.re (inner 𝕜 (f i) (L (f i))))]

/-! ### The scalar core inequality -/

