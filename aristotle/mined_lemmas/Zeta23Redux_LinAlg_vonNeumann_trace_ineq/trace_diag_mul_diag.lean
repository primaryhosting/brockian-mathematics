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

lemma trace_diag_mul_diag (lam xi : n → ℝ) (T : Matrix n n ℂ) :
    (diagonal (fun i => (lam i : ℂ)) * T * diagonal (fun j => (xi j : ℂ)) * Tᴴ).trace
      = ((∑ i, ∑ j, lam i * xi j * ‖T i j‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
    ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def]
  linear_combination ((lam i : ℂ) * (xi j : ℂ)) * Complex.mul_conj' (T i j)

/-- Rearrangement against a doubly stochastic matrix: for monovarying `mu`, `nu`, the bilinear
form `∑ i, ∑ j, mu i * nu j * S i j` is maximised at the identity.  This is Birkhoff's theorem
combined with the rearrangement inequality. -/
