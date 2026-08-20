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

lemma sum_sq_norm_col (T : Matrix n n ℂ) (h : Tᴴ * T = 1) (j : n) :
    ∑ i, ‖T i j‖ ^ 2 = 1 := by
  have h1 : (Tᴴ * T) j j = 1 := by rw [h]; simp
  have h2 : ((∑ i, ‖T i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h1]; simp [Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm, Complex.mul_conj']
  exact_mod_cast h2

/-- The basic bilinear identity: the trace of `diagonal lam * T * diagonal xi * Tᴴ` is the real
bilinear form in `lam` and `xi` given by the entrywise squared moduli of `T`. -/
