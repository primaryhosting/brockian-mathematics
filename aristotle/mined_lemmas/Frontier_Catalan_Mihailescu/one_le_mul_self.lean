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

private lemma one_le_mul_self {n : ℤ} (h : n ≠ 0) : 1 ≤ n * n := by
  have h1 : 1 ≤ |n| := Int.one_le_abs (by omega)
  nlinarith [abs_mul_abs_self n]

/-- Every unit of `ℤ[i]` has order dividing `4`. -/
