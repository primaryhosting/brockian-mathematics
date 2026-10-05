/-
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The doubling endomorphism `P ↦ 2 • P` of an additive commutative group. -/

theorem isWeilHeight_int_sq : IsWeilHeight ℤ (fun n => ((n : ℝ)) ^ 2) where
  translate := fun Q => ⟨2 * ((Q : ℝ)) ^ 2, by
    intro P
    push_cast
    nlinarith [sq_nonneg ((P : ℝ) - (Q : ℝ))]⟩
  double := ⟨0, by
    intro P
    have : (((2 : ℕ) • P : ℤ) : ℝ) = 2 * (P : ℝ) := by simp
    rw [this]
    nlinarith [sq_nonneg ((P : ℝ))]⟩
  finite_le := by
    intro C
    apply Set.Finite.subset (Set.finite_Icc (-(max ⌈C⌉ 1)) (max ⌈C⌉ 1))
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    have habs : ((|n| : ℤ) : ℝ) = |(n : ℝ)| := by push_cast [Int.cast_abs]; ring
    have h1 : |n| ≤ ⌈C⌉ ∨ |n| ≤ 1 := by
      rcases le_or_gt |(n : ℝ)| 1 with h | h
      · right
        have : ((|n| : ℤ) : ℝ) ≤ 1 := by rw [habs]; exact h
        exact_mod_cast this
      · left
        have hle : ((|n| : ℤ) : ℝ) ≤ C := by
          rw [habs]
          nlinarith [abs_nonneg (n : ℝ), sq_abs (n : ℝ)]
        have : ((|n| : ℤ) : ℝ) ≤ (⌈C⌉ : ℝ) := le_trans hle (Int.le_ceil C)
        exact_mod_cast this
    simp only [Set.mem_Icc]
    rcases abs_cases n with ⟨h, _⟩ | ⟨h, _⟩ <;> rcases h1 with h1 | h1 <;>
      simp only [le_max_iff] <;> omega

