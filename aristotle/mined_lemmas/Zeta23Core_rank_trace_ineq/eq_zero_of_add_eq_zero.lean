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

lemma eq_zero_of_add_eq_zero {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (h : A + B = 0) : A = 0 := by
  refine posSemidef_eq_zero_of_rtr_eq_zero hA (le_antisymm ?_ (rtr_nonneg hA))
  have h0 : rtr A + rtr B = 0 := by
    rw [← rtr_add, h]
    simp [rtr]
  linarith [rtr_nonneg hB]

/-- If `T` is positive semidefinite and `Kᴴ T K = 0` then `T K = 0`. -/
