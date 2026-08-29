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
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The real part of the trace of a matrix. -/

lemma eigenvectorUnitary_conjTranspose_mul (hA : A.IsHermitian) :
    ((hA.eigenvectorUnitary : Matrix n n 𝕜))ᴴ * (hA.eigenvectorUnitary : Matrix n n 𝕜) = 1 := by
  have h := hA.eigenvectorUnitary.2
  rw [Matrix.mem_unitaryGroup_iff'] at h
  simpa [Matrix.star_eq_conjTranspose] using h

