import Mathlib

/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped ComplexOrder
open Matrix

set_option maxHeartbeats 1000000

namespace Zeta23Core

variable {n : Type*} [Fintype n] {𝕜 : Type*} [RCLike 𝕜]

/-- The squared Frobenius norm of a matrix: `‖M‖_F² = Re tr(Mᴴ M)`. -/

noncomputable def posIndex [DecidableEq n] {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) : ℕ :=
  Fintype.card {i // 0 < hQ.eigenvalues i}

/-! ### Elementary facts about the squared Frobenius norm -/

