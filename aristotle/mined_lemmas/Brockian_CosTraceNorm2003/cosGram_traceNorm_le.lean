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

theorem cosGram_traceNorm_le {n : ℕ} (θ : Fin n → ℝ) : traceNorm (cosGram θ) ≤ (n : ℝ) :=
  le_of_eq (CosTraceNorm2003 θ).2.2

/-- For an arbitrary matrix of cosines, the trace is bounded in absolute value by `n`. -/
