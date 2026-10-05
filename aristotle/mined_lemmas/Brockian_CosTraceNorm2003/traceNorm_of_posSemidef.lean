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

theorem traceNorm_of_posSemidef {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) :
    traceNorm A = A.trace := by
  rw [traceNorm, CFC.abs_of_nonneg A hA.nonneg]

/-- The cosine Gram matrix is the Gram matrix of the unit vectors `(cos θ j, sin θ j)`. -/
