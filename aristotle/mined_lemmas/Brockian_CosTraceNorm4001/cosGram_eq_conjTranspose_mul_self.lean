/-
# Cos Trace Norm 4001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm4001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cos Trace Norm 4001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm4001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Matrix
open scoped MatrixOrder

/-- The `4001 × 4001` real "cosine Gram matrix" attached to a family of angles
`θ : Fin 4001 → ℝ`, with entries `cos (θ i - θ j)`. -/

theorem cosGram_eq_conjTranspose_mul_self (θ : Fin 4001 → ℝ) :
    cosGram θ = (angleFrame θ)ᴴ * (angleFrame θ) := by
  ext i j
  simp [cosGram, angleFrame, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_sub]

/-- The cosine Gram matrix is positive semidefinite. -/
