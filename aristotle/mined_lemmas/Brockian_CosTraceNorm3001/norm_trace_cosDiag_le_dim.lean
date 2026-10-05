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

theorem norm_trace_cosDiag_le_dim (θ : Fin n → ℝ) (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * Uᴴ = 1) : ‖Matrix.trace (U * cosDiag θ * Uᴴ)‖ ≤ n := by
  obtain ⟨-, h₁, h₂⟩ := CosTraceNorm3001 θ U hU
  exact h₁.trans h₂

/-- Sharpness: the dimension bound is attained at the zero phases. -/
