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

def FLTPositive : Prop :=
  ∀ n x y z : ℕ, 2 < n → 0 < x → 0 < y → 0 < z → x ^ n + y ^ n ≠ z ^ n

/-- The positive-integer phrasing of Fermat's Last Theorem agrees with Mathlib's
`FermatLastTheorem` (which is phrased via nonvanishing of `a`, `b`, `c` and `n ≥ 3`). -/
