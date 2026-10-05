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

theorem norm_trace_mul_hermCos_le_sum {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {V : Matrix n n ℂ} (hV : V ∈ Matrix.unitaryGroup n ℂ) :
    ‖(V * hermCos hA).trace‖ ≤ ∑ i, |Real.cos (hA.eigenvalues i)| := by
  have h := norm_trace_mul_conj_diagonal_le (U := (hA.eigenvectorUnitary : Matrix n n ℂ))
    hA.eigenvectorUnitary.2 hV (fun i => ((Real.cos (hA.eigenvalues i) : ℝ) : ℂ))
  simpa [hermCos, Matrix.mul_assoc, -Complex.ofReal_cos, Complex.norm_real] using h

/-- **Cos Trace Norm 4001.**
For every Hermitian matrix `A` over `ℂ`, the trace norm of `cos A` is at most the dimension.
The statement is given in the dual (variational) form of the trace norm,
`‖M‖₁ = sup { ‖tr (V * M)‖ : V unitary }`: every unitary test `V` satisfies
`‖tr (V * cos A)‖ ≤ card n`. -/
