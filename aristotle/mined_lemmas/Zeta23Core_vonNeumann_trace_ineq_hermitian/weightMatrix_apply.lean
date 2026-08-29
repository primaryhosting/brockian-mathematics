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
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Finset Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix of squared moduli of the entries of `W`. If `W` is unitary this is a doubly
stochastic matrix. -/

@[simp] lemma weightMatrix_apply (W : Matrix n n 𝕜) (j k : n) :
    weightMatrix W j k = ‖W j k‖ ^ 2 := rfl

/-- The squared-modulus matrix of a unitary matrix is doubly stochastic. -/
