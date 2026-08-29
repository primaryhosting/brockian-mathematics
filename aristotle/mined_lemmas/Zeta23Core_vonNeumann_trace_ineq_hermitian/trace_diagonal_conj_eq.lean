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

theorem trace_diagonal_conj_eq (W : Matrix n n 𝕜) (a b : n → ℝ) :
    Matrix.trace (diagonal (RCLike.ofReal ∘ a) * W * diagonal (RCLike.ofReal ∘ b) * star W)
      = ((∑ j, ∑ k, a j * b k * ‖W j k‖ ^ 2 : ℝ) : 𝕜) := by
  rw [Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.star_apply]
  simp only [Function.comp_apply, RCLike.star_def]
  rw [show (a j : 𝕜) * W j k * (b k) * (starRingEnd 𝕜) (W j k)
      = (a j : 𝕜) * (b k) * (W j k * (starRingEnd 𝕜) (W j k)) by ring, RCLike.mul_conj]

/-- Conjugating by a unitary and cycling the trace: `tr ((U Dₐ U*)(V D_b V*)) = tr (Dₐ W D_b W*)`
for `W = U* V`. -/
