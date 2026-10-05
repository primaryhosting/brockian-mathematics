import Mathlib

/-!
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
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

namespace Zeta23Redux.LinAlg

open Matrix Unitary

variable {d : ℕ}

/-! ## Basic real-valued trace functionals -/

/-- The real part of the trace of a matrix. -/

lemma frobSq_specM (hA : A.IsHermitian) (f : ℝ → ℝ) :
    frobSq (specM hA f) = ∑ i, (f (hA.eigenvalues i)) ^ 2 := by
  have h : frobSq (specM hA f) = rtrace (specM hA f * specM hA f) := by
    unfold frobSq rtrace
    rw [(specM_herm hA f).eq]
  rw [h, specM_mul, rtrace_specM]
  simp [sq]

