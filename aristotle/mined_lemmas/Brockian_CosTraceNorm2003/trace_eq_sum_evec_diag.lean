/-
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped ComplexOrder

namespace Brockian

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The `i`-th singular value of a complex square matrix `A`: the square root of the `i`-th
eigenvalue of the positive semidefinite matrix `Aᴴ * A`. -/

lemma trace_eq_sum_evec_diag (A : Matrix n n ℂ) :
    A.trace = ∑ i, star (evec A i) ⬝ᵥ (A *ᵥ evec A i) := by
  set hB := isHermitian_conjTranspose_mul_self A
  set U : Matrix n n ℂ := (hB.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  have hUU : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 (hB.eigenvectorUnitary).2
  have hcol : ∀ i : n, (fun k => U k i) = evec A i := by
    intro i
    funext k
    simp [hUdef, evec]
  have htr : (Uᴴ * A * U).trace = A.trace := by
    rw [Matrix.trace_mul_cycle, hUU, Matrix.one_mul]
  rw [← htr, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply]
  rw [conjTranspose_mul_mul_apply_diag, hcol]

/-- **Trace bound**: the absolute value of the trace of a complex square matrix is at most its
trace norm, `|tr A| ≤ ‖A‖₁`. -/
