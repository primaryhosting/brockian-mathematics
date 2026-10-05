import Mathlib

/-!
# Cos Trace Norm 4001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm4001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Finset

/-- The `4001 × 4001` cosine-difference (Gram) matrix attached to a family of phases
`θ : Fin 4001 → ℝ`, given by `G i j = cos (θ i - θ j)`. -/

noncomputable def cosGram4001 (θ : Fin 4001 → ℝ) : Matrix (Fin 4001) (Fin 4001) ℝ :=
  Matrix.of fun i j => Real.cos (θ i - θ j)

/-- The quadratic form of the cosine-difference matrix is a sum of two squares. -/
