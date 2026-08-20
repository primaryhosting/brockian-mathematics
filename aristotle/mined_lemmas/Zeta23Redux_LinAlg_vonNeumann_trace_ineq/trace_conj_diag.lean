/-
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open Finset

namespace Zeta23Redux.LinAlg

/-- Abel summation / Hardy–Littlewood–Pólya: if `m` is decreasing on `range d` and the partial
sums of `f` are dominated by those of `g`, with equal total sums, then `∑ m f ≤ ∑ m g`. -/

lemma trace_conj_diag {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ) (x y : Fin d → ℝ) :
    Matrix.trace (Matrix.diagonal (fun i => (x i : ℂ)) * W *
        Matrix.diagonal (fun j => (y j : ℂ)) * star W)
      = ∑ i, ∑ j, ((x i * y j * Complex.normSq (W i j) : ℝ) : ℂ) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, ite_mul, zero_mul,
    Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, RCLike.star_def]
  ring

/-- Rows of the entrywise squared-modulus matrix of a unitary matrix sum to one. -/
