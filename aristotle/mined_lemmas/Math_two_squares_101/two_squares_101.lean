/-!
# Two Squares 101
Category: Pure Mathematics
Target: Math.two_squares_101
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **The prime `101` is a sum of two squares.**

Primality of `101` is spelled out elementarily (`2 ≤ 101` and every proper divisor equals `1`),
so that the statement is self-contained; the sum-of-two-squares decomposition is
`101 = 1 ^ 2 + 10 ^ 2`.

(See `Math.two_squares_101_prime` for the version phrased with Mathlib's `Nat.Prime`.) -/

theorem two_squares_101 :
    (2 ≤ 101 ∧ ∀ m < 101, m ∣ 101 → m = 1) ∧ ∃ a b : Nat, 101 = a ^ 2 + b ^ 2 :=
  ⟨⟨by decide, by decide⟩, 1, 10, rfl⟩

end Math

import Mathlib
import RequestProject.TwoSquares101

/-!
# Two Squares 101 — Mathlib-flavoured restatement

The file `RequestProject/TwoSquares101.lean` must begin with a fixed header comment, which
forces it to be import-free (Lean requires `import` lines to come first in a file).  This file
records the same result phrased with Mathlib's `Nat.Prime`, derived from `Math.two_squares_101`.
-/

namespace Math

/-- The prime `101` is a sum of two squares, stated with Mathlib's `Nat.Prime`. -/
