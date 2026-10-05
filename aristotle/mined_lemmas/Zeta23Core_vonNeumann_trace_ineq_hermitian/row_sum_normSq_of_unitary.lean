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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option grind.warning false

namespace Zeta23Core

open Matrix Finset

/-- Two antitone functions on a linear order monovary. -/

theorem row_sum_normSq_of_unitary {W : Matrix n n 𝕜} (hW : W * star W = 1) (j : n) :
    ∑ k, ‖W j k‖ ^ 2 = 1 := by
  have hj : ∑ k, W j k * (starRingEnd 𝕜) (W j k) = 1 := by
    have := congrArg (fun M : Matrix n n 𝕜 => M j j) hW
    simpa only [Matrix.mul_apply, Matrix.one_apply_eq, Matrix.star_apply, RCLike.star_def]
      using this
  have h : ((∑ k, ‖W j k‖ ^ 2 : ℝ) : 𝕜) = 1 := by
    rw [← hj]
    push_cast
    exact Finset.sum_congr rfl fun k _ => (RCLike.mul_conj (W j k)).symm
  exact_mod_cast h

/-- The column sums of squared moduli of a unitary matrix are `1`. -/
