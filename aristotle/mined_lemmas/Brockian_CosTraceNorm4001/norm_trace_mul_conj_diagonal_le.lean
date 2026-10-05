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

theorem norm_trace_mul_conj_diagonal_le {U V : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (hV : V ∈ Matrix.unitaryGroup n ℂ) (d : n → ℂ) :
    ‖(V * (U * diagonal d * star U)).trace‖ ≤ ∑ i, ‖d i‖ := by
  have hW : (star U * V * U) ∈ Matrix.unitaryGroup n ℂ :=
    mul_mem (mul_mem (Unitary.star_mem hU) hV) hU
  have h1 : (V * (U * diagonal d * star U)).trace = ((star U * V * U) * diagonal d).trace := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.trace_mul_cycle (V * U) (diagonal d) (star U)]
    simp [Matrix.mul_assoc]
  rw [h1]
  exact norm_trace_mul_diagonal_le hW d

/-- Key duality step: testing `hermCos hA` against an arbitrary unitary gives the sharp bound
by the sum of the absolute values of the cosines of the eigenvalues. -/
