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

lemma normSq_row_sum {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ) (h : W * star W = 1) (i : Fin d) :
    ∑ j, Complex.normSq (W i j) = 1 := by
  have h2 := congrFun (congrFun h i) i
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, RCLike.star_def] at h2
  have h3 : ∑ j, ((Complex.normSq (W i j) : ℝ) : ℂ) = 1 := by
    rw [← h2]
    exact Finset.sum_congr rfl fun j _ => by rw [Complex.mul_conj]
  have h4 : ((∑ j, Complex.normSq (W i j) : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    push_cast; simpa using h3
  exact_mod_cast h4

/-- Columns of the entrywise squared-modulus matrix of a unitary matrix sum to one. -/
