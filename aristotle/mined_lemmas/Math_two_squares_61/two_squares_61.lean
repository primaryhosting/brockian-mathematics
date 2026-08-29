/-!
# Two Squares 61
Category: Pure Mathematics
Target: Math.two_squares_61
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **The prime `61` is a sum of two squares.**

The first component states that `61` is prime, spelled out elementarily as
`1 < 61` together with "every proper divisor of `61` equals `1`"; the second
component exhibits `61 = 5 ^ 2 + 6 ^ 2`.

The required header comment must be the first thing in this file, which Lean does
not allow to be followed by `import` commands, so this file is stated and proved
using only Lean core.  The same result phrased with Mathlib's `Nat.Prime` and
derived from Mathlib's two-square theorem `Nat.Prime.sq_add_sq` is in
`RequestProject/TwoSquares61Mathlib.lean`. -/

theorem two_squares_61 :
    (1 < 61 ∧ ∀ m < 61, m ∣ 61 → m = 1) ∧ ∃ a b : Nat, 61 = a ^ 2 + b ^ 2 :=
  ⟨⟨by decide, by decide⟩, ⟨5, 6, rfl⟩⟩

end Math

import Mathlib

/-!
# Two Squares 61 (Mathlib phrasing)

Companion to `RequestProject/Math.lean`: the statement "the prime `61` is a sum of
two squares", phrased with Mathlib's `Nat.Prime`, both with explicit witnesses and
via Mathlib's two-square theorem `Nat.Prime.sq_add_sq`.
-/

namespace Math

/-- `61` is prime and `61 = 5 ^ 2 + 6 ^ 2`. -/
