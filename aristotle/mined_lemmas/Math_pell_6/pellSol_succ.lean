import Mathlib

/-!
# Pell's equation `x² - 6·y² = 1`: infinitely many solutions

This file complements `RequestProject/Main.lean` (which contains the target
statement `Math.pell_6`) with the Mathlib-based development of the same
equation: iterating the fundamental automorphism attached to the fundamental
solution `(5, 2)` produces infinitely many integer solutions.
-/

namespace Math

/-- Multiplication by the fundamental unit `5 + 2√6`, in coordinates:
`(x, y) ↦ (5x + 12y, 2x + 5y)`. -/

@[simp] theorem pellSol_succ (n : ℕ) : pellSol (n + 1) = pellStep (pellSol n) := rfl

/-- `pellStep` preserves the Pell form `x² - 6y²`. -/
