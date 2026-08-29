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

noncomputable def cosGram (θ : Fin 4001 → ℝ) : Matrix (Fin 4001) (Fin 4001) ℝ :=
  fun i j => Real.cos (θ i - θ j)

/-- The `2 × 4001` matrix whose columns are the unit vectors `(cos θ j, sin θ j)`. -/
