/-!
# Two Squares 89
Category: Pure Mathematics
Target: Math.two_squares_89
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 89.**  The number `89` is prime (stated elementarily: it is at least `2`
and its only divisors are `1` and itself) and it is a sum of two squares, namely
`89 = 5 ^ 2 + 8 ^ 2`.

This file is deliberately import-free (the required header comment above is a module docstring,
which must precede any `import`), so primality is phrased directly rather than via
`Nat.Prime`; the file `RequestProject/TwoSquares89Mathlib.lean` derives the `Nat.Prime`
version from this theorem. -/

theorem two_squares_89 :
    2 ≤ 89 ∧ (∀ m : Nat, m ∣ 89 → m = 1 ∨ m = 89) ∧ ∃ a b : Nat, 89 = a ^ 2 + b ^ 2 := by
  refine ⟨by decide, fun m hm => ?_, 5, 8, by decide⟩
  have h : m ≤ 89 := Nat.le_of_dvd (by decide) hm
  have key : ∀ k < 90, k ∣ 89 → k = 1 ∨ k = 89 := by decide
  exact key m (by omega) hm

end Math

import Mathlib
import RequestProject.TwoSquares89

/-!
# Two Squares 89 — Mathlib phrasing

`Nat.Prime`-flavoured restatement of `Math.two_squares_89`.
-/

namespace Math

/-- The prime `89` is a sum of two squares: `89 = 5 ^ 2 + 8 ^ 2`. -/
