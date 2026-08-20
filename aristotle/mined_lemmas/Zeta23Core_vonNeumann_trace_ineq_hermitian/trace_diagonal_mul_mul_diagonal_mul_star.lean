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

theorem trace_diagonal_mul_mul_diagonal_mul_star (α β : n → ℝ) (W : Matrix n n 𝕜) :
    trace (diagonal (RCLike.ofReal ∘ α) * W * (diagonal (RCLike.ofReal ∘ β) * star W))
      = RCLike.ofReal (∑ j, ∑ k, α j * β k * ‖W j k‖ ^ 2) := by
  rw [trace]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [diag_apply, Matrix.mul_apply, diagonal_apply, Matrix.star_apply,
    Function.comp_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : W j k * (starRingEnd 𝕜) (W j k) = (‖W j k‖ : 𝕜) ^ 2 := RCLike.mul_conj _
  rw [RCLike.star_def]
  linear_combination (RCLike.ofReal (α j) * RCLike.ofReal (β k) : 𝕜) * h

/-- For Hermitian `A`, `B` with eigenvalue lists `α`, `β`, the trace of `A * B` equals
`∑ j k, α j * β k * |W j k|²` for the unitary `W = Uᴴ V` built from the eigenvector
unitaries of `A` and `B`. -/
