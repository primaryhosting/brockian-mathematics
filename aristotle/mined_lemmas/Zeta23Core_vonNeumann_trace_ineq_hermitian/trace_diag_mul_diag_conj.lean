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

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Core

open Matrix Finset

/-! ### A rearrangement bound for doubly stochastic matrices -/

/-- If `a` and `b` monovary, then the bilinear form `∑ j k, D j k * (a j * b k)` attached to a
doubly stochastic matrix `D` is at most `∑ i, a i * b i`.  This is the combinatorial heart of the
von Neumann trace inequality: it follows from Birkhoff's theorem together with the rearrangement
inequality. -/

lemma trace_diag_mul_diag_conj (a b : n → ℝ) (M : Matrix n n 𝕜) :
    Matrix.trace (Matrix.diagonal (fun i => (a i : 𝕜)) * M *
        Matrix.diagonal (fun i => (b i : 𝕜)) * Mᴴ)
      = ∑ j, ∑ k, ((a j * b k * ‖M j k‖ ^ 2 : ℝ) : 𝕜) := by
  have hprod : Matrix.diagonal (fun i => (a i : 𝕜)) * M * Matrix.diagonal (fun i => (b i : 𝕜))
      = Matrix.of (fun j k => (a j : 𝕜) * M j k * (b k : 𝕜)) := by
    ext j k
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rfl
  rw [hprod, Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.conjTranspose_apply, Matrix.of_apply]
  have h2 : M j k * star (M j k) = ((‖M j k‖ : 𝕜)) ^ 2 := by
    rw [RCLike.star_def, RCLike.mul_conj]
  push_cast
  linear_combination ((a j : 𝕜) * (b k : 𝕜)) * h2

omit [DecidableEq n] in
/-- Moving the conjugations onto a single unitary factor inside a trace. -/
