import Mathlib

/-!
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Matrix

namespace Brockian

/-- The cosine Gram matrix of a family of angles `x : Fin n → ℝ`:
its `(i, j)` entry is `cos (x i - x j)`. -/

noncomputable def cosSinRows {n : ℕ} (x : Fin n → ℝ) : Matrix (Fin 2) (Fin n) ℝ :=
  Matrix.of fun k j => if k = 0 then Real.cos (x j) else Real.sin (x j)

