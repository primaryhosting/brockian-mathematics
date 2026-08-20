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

lemma sqAbsMatrix_mem_doublyStochastic {W : Matrix n n 𝕜} (h1 : W * star W = 1)
    (h2 : star W * W = 1) : sqAbsMatrix W ∈ doublyStochastic ℝ n := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun j k => by simp, fun j => ?_, fun k => ?_⟩
  · have hj := congrFun (congrFun h1 j) j
    simp only [Matrix.mul_apply, Matrix.star_apply, RCLike.star_def, Matrix.one_apply_eq] at hj
    have : ((∑ k, ‖W j k‖ ^ 2 : ℝ) : 𝕜) = 1 := by
      push_cast
      rw [← hj]
      exact Finset.sum_congr rfl fun k _ => (RCLike.mul_conj (W j k)).symm
    simpa using (by exact_mod_cast this : (∑ k, ‖W j k‖ ^ 2 : ℝ) = 1)
  · have hk := congrFun (congrFun h2 k) k
    simp only [Matrix.mul_apply, Matrix.star_apply, RCLike.star_def, Matrix.one_apply_eq] at hk
    have : ((∑ j, ‖W j k‖ ^ 2 : ℝ) : 𝕜) = 1 := by
      push_cast
      rw [← hk]
      exact Finset.sum_congr rfl fun j _ => (RCLike.conj_mul (W j k)).symm
    simpa using (by exact_mod_cast this : (∑ j, ‖W j k‖ ^ 2 : ℝ) = 1)

end Weights

section Rearrangement

variable {N : Type*} [Fintype N] [DecidableEq N] [LinearOrder N]

/-- For a doubly stochastic weight matrix `S` and antitone `a`, `b`, the weighted sum
`∑ j k, a j * b k * S j k` is at most the aligned sum `∑ i, a i * b i`. -/
