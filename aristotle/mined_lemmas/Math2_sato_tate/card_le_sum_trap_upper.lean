/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Set MeasureTheory intervalIntegral
open scoped Real

namespace Math2

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

lemma card_le_sum_trap_upper (θ : ℕ → ℝ) (X : ℕ) {α β ε : ℝ} (hε : 0 < ε) :
    ((((primesBelow X).filter fun p => θ p ∈ Icc α β).card : ℝ))
      ≤ ∑ p ∈ primesBelow X, trap (α - ε) (β + ε) ε (θ p) := by
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_le_sum fun p _ => ?_
  by_cases h : θ p ∈ Icc α β
  · have h1 := trap_eq_one (u := α - ε) (v := β + ε) hε (by simp; exact h.1) (by simp; exact h.2)
    simp [h, h1]
  · simp [h, trap_nonneg]

