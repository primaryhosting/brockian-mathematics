/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- The radical of `n`: the product of the distinct prime factors of `n`.
By convention `rad 0 = rad 1 = 1`. -/

theorem abcExceptional_finite_of_bounded {eps : ℝ} {C : ℕ}
    (h : ∀ t ∈ abcExceptional eps, t.2.2 ≤ C) : (abcExceptional eps).Finite := by
  apply Set.Finite.subset
    (((Set.finite_Iic C).prod ((Set.finite_Iic C).prod (Set.finite_Iic C))))
  intro t ht
  have hc := h t ht
  obtain ⟨ha, hb, -, hsum, -⟩ := ht
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Set.mem_Iic] <;> omega

/-- If the exceptional set for `ε` is finite, then `c` is bounded on it. -/
