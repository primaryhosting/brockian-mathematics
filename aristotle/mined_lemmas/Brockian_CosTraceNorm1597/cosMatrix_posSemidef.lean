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

lemma cosMatrix_posSemidef {n : ℕ} (x : Fin n → ℝ) : (cosMatrix x).PosSemidef := by
  rw [cosMatrix_eq_gram]
  exact Matrix.posSemidef_conjTranspose_mul_self _

