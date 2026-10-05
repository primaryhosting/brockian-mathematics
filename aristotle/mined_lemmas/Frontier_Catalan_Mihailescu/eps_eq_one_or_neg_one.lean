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

lemma eps_eq_one_or_neg_one {m : ℕ} (h : Odd m) : eps m = 1 ∨ eps m = -1 := by
  have h1 := eps_sq_of_odd h
  have h2 : (eps m - 1) * (eps m + 1) = 0 := by nlinarith
  rcases mul_eq_zero.1 h2 with h' | h'
  · left; linarith
  · right; linarith

/-- Binomial expansion of the imaginary part of `(a + i) ^ r`. -/
