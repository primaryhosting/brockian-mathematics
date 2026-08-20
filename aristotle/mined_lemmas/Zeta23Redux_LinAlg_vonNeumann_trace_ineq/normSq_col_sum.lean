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

lemma normSq_col_sum {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ) (h : star W * W = 1) (j : Fin d) :
    ∑ i, Complex.normSq (W i j) = 1 := by
  have h2 := congrFun (congrFun h j) j
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, RCLike.star_def] at h2
  have h3 : ∑ i, ((Complex.normSq (W i j) : ℝ) : ℂ) = 1 := by
    rw [← h2]
    exact Finset.sum_congr rfl fun i _ => by rw [Complex.normSq_eq_conj_mul_self]
  have h4 : ((∑ i, Complex.normSq (W i j) : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    push_cast; simpa using h3
  exact_mod_cast h4

/-- Diagonalising both Hermitian matrices turns `trace (A * B)` into a conjugated diagonal
trace, with `W = Uᴴ V` the unitary intertwining the two eigenbases. -/
