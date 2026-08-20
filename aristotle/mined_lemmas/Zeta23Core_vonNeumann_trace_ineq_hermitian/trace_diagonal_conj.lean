/-
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
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

namespace Zeta23Core

open Matrix Finset

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix of squared absolute values of the entries of a unitary matrix is doubly
stochastic. -/

lemma trace_diagonal_conj (da db : n → ℝ) (W : Matrix n n 𝕜) :
    Matrix.trace (diagonal (RCLike.ofReal ∘ da) * W * diagonal (RCLike.ofReal ∘ db) * star W)
      = ∑ p, ∑ q, ((da p * db q * ‖W p q‖ ^ 2 : ℝ) : 𝕜) := by
  have key : diagonal (RCLike.ofReal ∘ da) * W * diagonal (RCLike.ofReal ∘ db)
      = Matrix.of (fun p q => ((da p : 𝕜)) * W p q * (db q : 𝕜)) := by
    ext p q
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp
  rw [key, Matrix.trace]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Matrix.of_apply, Matrix.star_apply, RCLike.star_def]
  push_cast
  rw [mul_assoc, mul_comm ((db q : 𝕜)) _, ← mul_assoc, mul_assoc ((da p : 𝕜)) (W p q),
    RCLike.mul_conj]
  ring

/-- The trace of `A * B` for Hermitian `A`, `B`, written in terms of the eigenvalues and the
unitary `W` connecting the two eigenbases. -/
