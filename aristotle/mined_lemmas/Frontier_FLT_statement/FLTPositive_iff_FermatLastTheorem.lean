/-
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace Frontier

/-- Fermat's Last Theorem, stated directly in terms of positive integers:
for every exponent `n > 2` there are no positive natural numbers `x, y, z`
with `x ^ n + y ^ n = z ^ n`. -/

theorem FLTPositive_iff_FermatLastTheorem : FLTPositive ↔ FermatLastTheorem := by
  constructor
  · intro h n hn a b c ha hb hc
    exact h n a b c (by omega) (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)
      (Nat.pos_of_ne_zero hc)
  · intro h n x y z hn hx hy hz
    exact h n (by omega) x y z hx.ne' hy.ne' hz.ne'

/-- Base case `n = 3`: no positive integers satisfy `x ^ 3 + y ^ 3 = z ^ 3`. -/
