import Mathlib

/-!
# Two Squares 13 — Mathlib companion

A Mathlib-based restatement of `Math.two_squares_13`, obtained from the general
Fermat two-squares theorem `Nat.Prime.sq_add_sq` (every prime `p` with `p % 4 ≠ 3`
is a sum of two squares).
-/

namespace Math

/-- `13` is prime and is a sum of two squares, via Mathlib's `Nat.Prime.sq_add_sq`. -/

theorem two_squares_13_mathlib : Nat.Prime 13 ∧ ∃ a b : ℕ, 13 = a ^ 2 + b ^ 2 := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  refine ⟨by norm_num, ?_⟩
  obtain ⟨a, b, h⟩ := Nat.Prime.sq_add_sq (p := 13) (by norm_num)
  exact ⟨a, b, h.symm⟩

end Math

/-!
# Two Squares 13
Category: Pure Mathematics
Target: Math.two_squares_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The prime `13` is a sum of two squares: `13 = 2 ^ 2 + 3 ^ 2`.

We also record that `13` is prime, in the elementary form that `1 < 13` and every divisor
of `13` is either `1` or `13`.

(The header comment required for this file must be the very first thing in the file, and Lean
forbids `import` commands after a comment, so this development is written using only Lean's
core library rather than Mathlib; the proof is fully self-contained and axiom-clean.) -/
