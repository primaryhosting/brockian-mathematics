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

open Matrix

/-- **Kraus maps are trace preserving.**

If a family of Kraus operators `E : K → Matrix n n ℂ` (over a finite index set `K`)
satisfies the completeness relation `∑ k, (E k)ᴴ * (E k) = 1`, then the associated
quantum channel `ρ ↦ ∑ k, E k * ρ * (E k)ᴴ` preserves the trace. -/
theorem kraus_trace_preserving
    {n K : Type*} [Fintype n] [DecidableEq n] [Fintype K]
    (E : K → Matrix n n ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1)
    (ρ : Matrix n n ℂ) :
    Matrix.trace (∑ k, E k * ρ * (E k)ᴴ) = Matrix.trace ρ := by
  rw [Matrix.trace_sum]
  have hk : ∀ k : K, Matrix.trace (E k * ρ * (E k)ᴴ)
      = Matrix.trace ((E k)ᴴ * E k * ρ) := by
    intro k
    rw [Matrix.trace_mul_comm (E k * ρ) ((E k)ᴴ), Matrix.mul_assoc]
  simp_rw [hk]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, hE, Matrix.one_mul]

end QC

