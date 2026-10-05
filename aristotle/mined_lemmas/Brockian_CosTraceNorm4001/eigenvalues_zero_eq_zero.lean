import Mathlib

/-!
# Cos Trace Norm 4001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm4001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset

namespace Brockian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Unfolding of the unitary conjugation star-algebra automorphism used by the matrix
spectral theorem. -/

theorem eigenvalues_zero_eq_zero (i : n) :
    (Matrix.isHermitian_zero (n := n) (α := ℂ)).eigenvalues i = 0 := by
  set hA := Matrix.isHermitian_zero (n := n) (α := ℂ) with hAdef
  have h := hA.spectral_theorem
  rw [conjStarAlgAut_apply] at h
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hU
  have h1 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hA.eigenvectorUnitary.2
  have hD : diagonal (Complex.ofReal ∘ hA.eigenvalues) = 0 := by
    have h3 := congrArg (fun M => star U * M * U) h
    simp only [Matrix.mul_assoc] at h3
    rw [← Matrix.mul_assoc (star U) U, h1, Matrix.one_mul] at h3
    simp at h3
    exact h3.symm
  simpa using congrFun (congrFun hD i) i

/-- The bound of `CosTraceNorm4001` is sharp: for `A = 0` we get `cos A = 1`, whose trace norm
is exactly `card n` (witnessed by the unitary `V = 1`). -/
