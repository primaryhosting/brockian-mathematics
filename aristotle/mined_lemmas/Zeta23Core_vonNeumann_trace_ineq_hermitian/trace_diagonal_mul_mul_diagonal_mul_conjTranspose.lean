/-
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module docstring `/-! ... -/` before `import`, so the header above is
-- written as a plain block comment; it is repeated verbatim as a module docstring below.)

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

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace of `Dₐ W D_b Wᴴ`, for diagonal matrices with real entries `a`, `b`, expands as
`∑ j k, a j * b k * ‖W j k‖ ^ 2`. -/

theorem trace_diagonal_mul_mul_diagonal_mul_conjTranspose
    (W : Matrix n n 𝕜) (a b : n → ℝ) :
    Matrix.trace (diagonal (fun j => (a j : 𝕜)) * W * diagonal (fun k => (b k : 𝕜)) * Wᴴ)
      = ∑ j, ∑ k, ((a j * b k * ‖W j k‖ ^ 2 : ℝ) : 𝕜) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.conjTranspose_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    ite_mul, zero_mul, mul_ite, mul_zero]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  have h : W j k * star (W j k) = ((‖W j k‖ ^ 2 : ℝ) : 𝕜) := by
    simpa [RCLike.star_def] using RCLike.mul_conj (W j k)
  push_cast at h ⊢
  linear_combination ((a j : 𝕜) * (b k)) * h

/-- The matrix of squared absolute values of the entries of a unitary matrix is doubly
stochastic. -/
