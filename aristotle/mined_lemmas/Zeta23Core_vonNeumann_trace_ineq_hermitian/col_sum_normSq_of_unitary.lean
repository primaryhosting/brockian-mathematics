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

theorem col_sum_normSq_of_unitary {W : Matrix n n 𝕜} (hW : star W * W = 1) (k : n) :
    ∑ j, ‖W j k‖ ^ 2 = 1 := by
  have hk : ∑ j, (starRingEnd 𝕜) (W j k) * W j k = 1 := by
    have := congrArg (fun M : Matrix n n 𝕜 => M k k) hW
    simpa only [Matrix.mul_apply, Matrix.one_apply_eq, Matrix.star_apply, RCLike.star_def]
      using this
  have h : ((∑ j, ‖W j k‖ ^ 2 : ℝ) : 𝕜) = 1 := by
    rw [← hk]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    exact (RCLike.mul_conj (W j k)).symm
  exact_mod_cast h

/-- The matrix of squared moduli of the entries of a unitary matrix is doubly stochastic. -/
