/-
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix

namespace Zeta23Redux.LinAlg

/-- **Rearrangement against a doubly stochastic matrix.** If `S` is doubly stochastic and
`mu`, `nu` are both antitone, then the bilinear form `∑ i j, mu i * S i j * nu j` is at most
the aligned sum `∑ i, mu i * nu i`.  Proved via Birkhoff's theorem plus the rearrangement
inequality. -/

theorem trace_diagonal_mul_conjTranspose {d : ℕ} (a b : Fin d → ℝ)
    (W : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace (diagonal (fun i => (a i : ℂ)) * W * diagonal (fun i => (b i : ℂ)) * Wᴴ)
      = ((∑ i, ∑ j, a i * b j * Complex.normSq (W i j) : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.conjTranspose_apply, Complex.ofReal_sum, Complex.ofReal_mul]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_ite_eq]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := Complex.mul_conj (W i j)
  simp only [starRingEnd_apply] at h
  linear_combination ((a i : ℂ) * (b j : ℂ)) * h

/-- For a unitary matrix `W`, the entrywise squared moduli form a doubly stochastic matrix. -/
