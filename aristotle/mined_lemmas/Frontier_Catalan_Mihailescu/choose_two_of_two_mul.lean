import Mathlib

/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-- The full Catalan–Mihăilescu statement: `8` and `9` are the only consecutive
perfect powers, i.e. the only solution of `x ^ p = y ^ q + 1` in integers
`x, y, p, q > 1` is `3 ^ 2 = 2 ^ 3 + 1`. -/

private lemma choose_two_of_two_mul (j : ℕ) : (2 * j).choose 2 = j * (2 * j - 1) := by
  have h : 2 * j * (2 * j - 1) = 2 * (j * (2 * j - 1)) := by ring
  rw [Nat.choose_two_right, h, Nat.mul_div_cancel_left _ (by norm_num)]

/-- If `2 ^ e` divides `C(r, 2)` then it divides `C(r, 2 * j) * j`.  This is the key
comparison of `2`-adic valuations of binomial coefficients, coming from the identity
`C(r, 2j) * C(2j, 2) = C(r, 2) * C(r - 2, 2j - 2)`. -/
