/-
/-!
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

open scoped BigOperators
open scoped Real

namespace Brockian

/-- The `n × n` real diagonal matrix whose `i`-th diagonal entry is `cos (θ * i)`. -/

noncomputable def cosDiag (n : ℕ) (θ : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i : Fin n => Real.cos (θ * i))

/-- The trace of `cosDiag n θ` is the cosine sum `∑ i < n, cos (θ * i)`. -/
