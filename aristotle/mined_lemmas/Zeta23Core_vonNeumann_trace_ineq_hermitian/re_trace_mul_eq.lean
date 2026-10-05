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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Finset Matrix

section Rearrangement

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Value of the bilinear form `M ↦ ∑ j, ∑ k, M j k * (a j * b k)` at a permutation matrix. -/

lemma re_trace_mul_eq (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re ((A * B).trace)
      = ∑ j, ∑ k, eigWeight hA hB j k * (hA.eigenvalues j * hB.eigenvalues k) := by
  rw [trace_mul_eq_ofReal hA hB, RCLike.ofReal_re]

end Weights

/-- **Von Neumann trace inequality, Hermitian case.**
For Hermitian matrices `A`, `B` over an `RCLike` field indexed by a finite type,
the real part of `tr (A * B)` is at most the sum of the products of their eigenvalues,
each family sorted in decreasing order (`Matrix.IsHermitian.eigenvalues₀`). -/
