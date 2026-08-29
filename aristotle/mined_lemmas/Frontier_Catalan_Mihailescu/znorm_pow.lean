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

lemma znorm_pow (z : GaussianInt) (n : ℕ) : (z ^ n).norm = z.norm ^ n := by
  induction n with
  | zero => simp [Zsqrtd.norm_def]
  | succ k ih => rw [pow_succ, Zsqrtd.norm_mul, ih, pow_succ]

/-- The core case of Lebesgue's theorem: odd exponent `r ≥ 3`. -/
