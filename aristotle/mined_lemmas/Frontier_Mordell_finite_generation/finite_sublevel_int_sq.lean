import Mathlib

/-!
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open scoped Classical

/-- Multiplication by `m : ℕ` on an additive commutative group, as a group homomorphism. -/

lemma finite_sublevel_int_sq (C : ℝ) : {n : ℤ | ((n : ℝ)) ^ 2 ≤ C}.Finite := by
  apply Set.Finite.subset (Set.finite_Icc (-⌈max 1 C⌉) ⌈max 1 C⌉)
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  have habs : |(n : ℝ)| ≤ (n : ℝ) ^ 2 ∨ |(n : ℝ)| ≤ 1 := by
    rcases le_or_gt |(n : ℝ)| 1 with h | h
    · exact Or.inr h
    · exact Or.inl (by nlinarith [sq_abs ((n : ℝ))])
  have h1 : |(n : ℝ)| ≤ max 1 C := by
    rcases habs with h | h
    · exact (h.trans hn).trans (le_max_right _ _)
    · exact h.trans (le_max_left _ _)
  have h2 : (|n| : ℝ) ≤ ((⌈max 1 C⌉ : ℤ) : ℝ) := le_trans h1 (Int.le_ceil _)
  have h3 : |n| ≤ (⌈max 1 C⌉ : ℤ) := by exact_mod_cast h2
  rw [abs_le] at h3
  exact Set.mem_Icc.mpr ⟨h3.1, h3.2⟩

/-- A concrete instance of the descent theorem: `ℤ`, with height `n ↦ n ^ 2` and `m = 2`,
satisfies all the hypotheses of `Frontier.fg_of_descent`. -/
