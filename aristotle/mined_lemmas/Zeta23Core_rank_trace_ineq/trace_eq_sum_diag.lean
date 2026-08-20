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

lemma trace_eq_sum_diag {ι : Type*} [Fintype ι] (M : Matrix n n 𝕜)
    (f : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 n)) :
    Matrix.trace M = ∑ i, inner 𝕜 (f i) (Matrix.toEuclideanLin M (f i)) := by
  rw [sum_diag_eq _ f (EuclideanSpace.basisFun n 𝕜)]
  simp [Matrix.trace, Matrix.diag, Matrix.toLpLin_apply, PiLp.inner_apply,
    EuclideanSpace.basisFun_apply, Matrix.mulVec_single]

