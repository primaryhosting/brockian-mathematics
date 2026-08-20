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

lemma inner_toEuclideanLin (M : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n) :
    inner 𝕜 x (Matrix.toEuclideanLin M x) = star (WithLp.ofLp x) ⬝ᵥ (M *ᵥ WithLp.ofLp x) := by
  simp only [PiLp.inner_apply, Matrix.toLpLin_apply, dotProduct, Pi.star_apply,
    RCLike.inner_apply, star_def]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

