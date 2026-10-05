import Mathlib

/-!
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped MatrixOrder

namespace Brockian

open Matrix

/-- The *cosine Gram matrix* of a family of phases `θ : Fin n → ℝ`:
its `(i, j)` entry is `cos (θ i - θ j)`. -/

noncomputable def traceNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (CFC.abs A).trace

/-- For a positive semidefinite matrix the trace norm coincides with the trace. -/
