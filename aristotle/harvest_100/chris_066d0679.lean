/-
# Kraus Trace Preserving
Category: Quantum Computing
Target: QC.kraus_trace_preserving
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kraus Trace Preserving
Category: Quantum Computing
Target: QC.kraus_trace_preserving
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix Finset

/-- **Kraus maps are trace preserving.**
If a finite family of Kraus operators `E : κ → Matrix n n ℂ` satisfies the completeness
relation `∑ k, (E k)ᴴ * (E k) = 1`, then the induced quantum channel
`ρ ↦ ∑ k, E k * ρ * (E k)ᴴ` preserves the trace. -/
theorem kraus_trace_preserving {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]
    (E : κ → Matrix n n ℂ) (hE : ∑ k, (E k)ᴴ * (E k) = 1) (ρ : Matrix n n ℂ) :
    Matrix.trace (∑ k, E k * ρ * (E k)ᴴ) = Matrix.trace ρ := by
  rw [Matrix.trace_sum]
  have h : ∀ k : κ, Matrix.trace (E k * ρ * (E k)ᴴ)
      = Matrix.trace ((E k)ᴴ * (E k) * ρ) := by
    intro k
    rw [Matrix.trace_mul_cycle, Matrix.mul_assoc]
  simp_rw [h]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, hE, Matrix.one_mul]

end QC

