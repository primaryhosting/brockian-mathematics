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

lemma sum_trap_lower_le_card (θ : ℕ → ℝ) (X : ℕ) {α β ε : ℝ} (hε : 0 < ε) :
    (∑ p ∈ primesBelow X, trap α β ε (θ p))
      ≤ ((((primesBelow X).filter fun p => θ p ∈ Icc α β).card : ℝ)) := by
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_le_sum fun p _ => ?_
  by_cases h : θ p ∈ Icc α β
  · simp [h, trap_le_one]
  · simp only [Set.mem_Icc, not_and_or, not_le] at h
    rcases h with h | h
    · rw [trap_eq_zero_left hε h.le]; positivity
    · rw [trap_eq_zero_right hε h.le]; positivity

