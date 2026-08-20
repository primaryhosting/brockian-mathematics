import Mathlib

/-!
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace Zeta23Redux.LinAlg

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The squared moduli along a row of a unitary matrix sum to `1`. -/

lemma sum_sq_norm_row (T : Matrix n n ℂ) (h : T * Tᴴ = 1) (i : n) :
    ∑ j, ‖T i j‖ ^ 2 = 1 := by
  have h1 : (T * Tᴴ) i i = 1 := by rw [h]; simp
  have h2 : ((∑ j, ‖T i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h1]; simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_conj']
  exact_mod_cast h2

/-- The squared moduli along a column of a unitary matrix sum to `1`. -/
