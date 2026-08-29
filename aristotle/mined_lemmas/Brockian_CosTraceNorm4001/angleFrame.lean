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

noncomputable def angleFrame (θ : Fin 4001 → ℝ) : Matrix (Fin 2) (Fin 4001) ℝ :=
  fun k j => if k = 0 then Real.cos (θ j) else Real.sin (θ j)

/-- The trace norm (Schatten 1-norm) of a real square matrix: the trace of the positive
semidefinite square root of `Mᴴ * M`, i.e. the sum of the singular values of `M`. -/
