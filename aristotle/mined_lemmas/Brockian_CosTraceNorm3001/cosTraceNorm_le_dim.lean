/-
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian

open Matrix Finset

variable {n : ℕ}

/-- The "cosine matrix" attached to a list of phases `θ : Fin n → ℝ`:
the diagonal complex matrix with entries `cos (θ i)`. -/

lemma cosTraceNorm_le_dim (θ : Fin n → ℝ) : cosTraceNorm θ ≤ n := by
  have : ∀ i ∈ (Finset.univ : Finset (Fin n)), |Real.cos (θ i)| ≤ 1 := by
    intro i _; exact Real.abs_cos_le_one (θ i)
  calc cosTraceNorm θ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum this
    _ = n := by simp

/--
**Cos Trace Norm 3001.**

For any phases `θ : Fin n → ℝ` and any unitary `U`, the trace of the unitary conjugate
`U * cosDiag θ * Uᴴ` is unitarily invariant, is bounded in absolute value by the trace norm
`∑ i, |cos (θ i)|`, and the trace norm itself is bounded by the dimension `n`.
-/
