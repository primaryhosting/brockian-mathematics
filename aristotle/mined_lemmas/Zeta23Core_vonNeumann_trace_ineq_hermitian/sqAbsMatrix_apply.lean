/-
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace Zeta23Core

open Matrix Finset

section Weights

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The entrywise squared-modulus matrix `j k ↦ ‖W j k‖ ^ 2` of a matrix `W`. -/

@[simp] lemma sqAbsMatrix_apply (W : Matrix n n 𝕜) (j k : n) :
    sqAbsMatrix W j k = ‖W j k‖ ^ 2 := rfl

/-- If `W` is unitary, its entrywise squared-modulus matrix is doubly stochastic. -/
