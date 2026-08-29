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

theorem CosTraceNorm2003 {n : ℕ} (θ : Fin n → ℝ) :
    (cosGram θ).PosSemidef ∧ (cosGram θ).trace = (n : ℝ) ∧ traceNorm (cosGram θ) = (n : ℝ) :=
  ⟨cosGram_posSemidef θ, cosGram_trace θ,
    (traceNorm_of_posSemidef (cosGram_posSemidef θ)).trans (cosGram_trace θ)⟩

/-- The trace norm of the cosine Gram matrix is bounded by the size of the matrix. -/
