/-
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

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

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The entrywise squared modulus of a unitary matrix is doubly stochastic. -/

lemma trace_star_diag_mul_diag (W : Matrix n n ℂ) (a b : n → ℝ) :
    Matrix.trace (star W * Matrix.diagonal (fun i => (a i : ℂ)) * W *
        Matrix.diagonal (fun j => (b j : ℂ)))
      = ∑ j, ∑ i, ((Complex.normSq (W i j) * (a i * b j) : ℝ) : ℂ) := by
  have h : star W * Matrix.diagonal (fun i => (a i : ℂ)) * W *
        Matrix.diagonal (fun j => (b j : ℂ))
      = (star W * Matrix.diagonal (fun i => (a i : ℂ))) *
        (W * Matrix.diagonal (fun j => (b j : ℂ))) := by
    simp [mul_assoc]
  rw [h, Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.star_apply]
  push_cast
  rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

/-- Reduction of the trace of a product of two diagonalised matrices. -/
