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

theorem trace_cosDiag (n : ℕ) (θ : ℝ) :
    (cosDiag n θ).trace = ∑ i : Fin n, Real.cos (θ * i) := by
  simp [cosDiag, Matrix.trace_diagonal]

/--
**Cos Trace Norm 1597.**

For the diagonal cosine matrix `cosDiag n θ` (diagonal entries `cos (θ * i)`, `i < n`):

* the absolute value of its trace is bounded by its trace norm, i.e. by the sum of the
  absolute values of its (diagonal) singular values;
* that trace norm is at most `n`;
* the bound is sharp: at `θ = 0` the trace itself equals `n`.

The key Mathlib ingredients are `Finset.abs_sum_le_sum_abs` and `Real.abs_cos_le_one`.
-/
