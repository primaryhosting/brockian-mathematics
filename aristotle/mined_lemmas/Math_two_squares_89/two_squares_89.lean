/-!
# Two Squares 89
Category: Pure Mathematics
Target: Math.two_squares_89
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Two squares for 89.**  The number `89` is prime — it is at least `2` and its only
divisors are `1` and `89` — and it is a sum of two squares, namely `89 = 8 ^ 2 + 5 ^ 2`.

(The required header comment must be the first thing in the file, which rules out any
`import` line here, so primality is spelled out directly rather than via `Nat.Prime`.
The file `TwoSquares89Mathlib.lean` derives the Mathlib-flavoured statement, with
`Nat.Prime 89`, from this one.) -/

theorem two_squares_89 :
    (2 ≤ 89 ∧ ∀ d : Nat, d ∣ 89 → d = 1 ∨ d = 89) ∧ ∃ a b : Nat, 89 = a ^ 2 + b ^ 2 := by
  refine ⟨⟨by decide, ?_⟩, 8, 5, by decide⟩
  intro d hd
  have h1 : d ≤ 89 := Nat.le_of_dvd (by decide) hd
  revert hd
  revert h1
  revert d
  decide

end Math

import Mathlib
import RequestProject.TwoSquares89

/-!
# Two Squares 89 — Mathlib phrasing

Restatement of `Math.two_squares_89` using Mathlib's `Nat.Prime`.
-/

namespace Math

/-- The prime `89` is a sum of two squares, phrased with Mathlib's `Nat.Prime`. -/
