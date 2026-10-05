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


open scoped BigOperators
open scoped Matrix

set_option maxRecDepth 10000

namespace Brockian

/-- The `n × n` real "cosine Gram matrix" with entries `cos (i θ - j θ)`. -/

theorem cosGram_traceNorm (n : ℕ) (theta : ℝ) :
    ∑ i, |(cosGram_isHermitian n theta).eigenvalues i| = n := by
  have hpos := cosGram_posSemidef n theta
  have h1 : ∑ i, |(cosGram_isHermitian n theta).eigenvalues i|
      = ∑ i, (cosGram_isHermitian n theta).eigenvalues i :=
    Finset.sum_congr rfl fun i _ => abs_of_nonneg (hpos.eigenvalues_nonneg i)
  have h2 := (cosGram_isHermitian n theta).trace_eq_sum_eigenvalues
  rw [cosGram_trace] at h2
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h2
  rw [h1, ← h2]

/--
**Cos Trace Norm 4001.**

The trace norm (Schatten 1-norm, i.e. the sum of the absolute values of the eigenvalues) of
the `4001 × 4001` matrix with entries `cos (i θ - j θ)` equals `4001`, for every angle `θ`.

The matrix is a Gram matrix of unit vectors in the plane, hence positive semidefinite, so its
trace norm coincides with its trace, which is `4001`.
-/
