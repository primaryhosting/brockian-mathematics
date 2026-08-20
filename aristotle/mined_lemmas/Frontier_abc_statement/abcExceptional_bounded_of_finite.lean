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

theorem abcExceptional_bounded_of_finite {eps : ℝ} (h : (abcExceptional eps).Finite) :
    ∃ C : ℕ, ∀ t ∈ abcExceptional eps, t.2.2 ≤ C := by
  obtain ⟨C, hC⟩ := (h.image (fun t => t.2.2)).bddAbove
  exact ⟨C, fun t ht => hC ⟨t, ht, rfl⟩⟩

/-- **Reduction of the `abc` conjecture to a boundedness statement.**

The `abc` conjecture (for every `ε > 0`, only finitely many coprime triples `a + b = c`
of positive integers satisfy `rad (a * b * c) ^ (1 + ε) < c`) is equivalent to the
statement that for every `ε > 0` the value of `c` is bounded along such triples. -/
