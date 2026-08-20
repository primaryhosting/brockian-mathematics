import Mathlib

/-!
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
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

namespace Zeta23Redux.LinAlg

open Matrix Finset

/-- Birkhoff + rearrangement: for antitone `mu`, `nu` and a doubly stochastic matrix `S`,
the bilinear form `∑ i j, S i j * (mu i * nu j)` is at most `∑ i, mu i * nu i`. -/

lemma trace_diagonal_mul_mul_diagonal_mul_conjTranspose {d : ℕ} (mu nu : Fin d → ℝ)
    (W : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (diagonal (fun i => (mu i : ℂ)) * W * diagonal (fun j => (nu j : ℂ)) * Wᴴ)
      = ((∑ i, ∑ j, ‖W i j‖ ^ 2 * (mu i * nu j) : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    mul_ite, mul_zero, Finset.sum_ite_eq']
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : W i j * (starRingEnd ℂ) (W i j) = ((‖W i j‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [Complex.star_def]
  linear_combination ((mu i : ℂ) * (nu j : ℂ)) * h

/-- The eigenvalues of a Hermitian matrix can always be listed in decreasing order:
there is a permutation `e` of the index type with `hA.eigenvalues ∘ e` antitone.
(This shows that the hypotheses of `vonNeumann_trace_ineq` below are satisfiable.) -/
