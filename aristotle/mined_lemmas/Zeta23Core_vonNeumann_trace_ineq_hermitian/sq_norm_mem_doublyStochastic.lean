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

section DoublyStochastic

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- Two antitone functions monovary. -/

theorem sq_norm_mem_doublyStochastic {𝕜 : Type*} [RCLike 𝕜] (W : Matrix n n 𝕜)
    (hW1 : W * star W = 1) (hW2 : star W * W = 1) :
    (fun j k => ‖W j k‖ ^ 2 : Matrix n n ℝ) ∈ doublyStochastic ℝ n := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => by positivity, fun j => ?_, fun k => ?_⟩
  · have h := congrFun (congrFun hW1 j) j
    rw [Matrix.mul_apply] at h
    simp only [Matrix.star_apply, RCLike.star_def, Matrix.one_apply_eq] at h
    have h' : (RCLike.ofReal (∑ k, ‖W j k‖ ^ 2) : 𝕜) = 1 := by
      rw [← h]; push_cast
      exact Finset.sum_congr rfl fun k _ => (RCLike.mul_conj _).symm
    exact_mod_cast h'
  · have h := congrFun (congrFun hW2 k) k
    rw [Matrix.mul_apply] at h
    simp only [Matrix.star_apply, RCLike.star_def, Matrix.one_apply_eq] at h
    have h' : (RCLike.ofReal (∑ j, ‖W j k‖ ^ 2) : 𝕜) = 1 := by
      rw [← h]; push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm]
      exact (RCLike.mul_conj _).symm
    exact_mod_cast h'

end DoublyStochastic

section Trace

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- Trace of `diag(α) * W * diag(β) * Wᴴ` in terms of the squared absolute values of the
entries of `W`. -/
