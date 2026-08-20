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

variable {d : ℕ}

/-- A bilinear form against a doubly stochastic matrix is bounded by the "sorted" pairing,
when both weight vectors are listed in the same (decreasing) order.

This is the Birkhoff + rearrangement step of von Neumann's trace inequality. -/

theorem trace_diag_conj (W : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d → ℝ) :
    Matrix.trace (diagonal (fun i => (a i : ℂ)) * W * diagonal (fun j => (b j : ℂ)) * star W)
      = ((∑ i, ∑ j, Complex.normSq (W i j) * (a i * b j) : ℝ) : ℂ) := by
  rw [Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_ite, mul_zero, Finset.sum_ite_eq,
    RCLike.star_def]
  linear_combination ((a i : ℂ) * (b j : ℂ)) * (Complex.mul_conj (W i j))

/-- The entrywise squared modulus of a unitary matrix is doubly stochastic. -/
