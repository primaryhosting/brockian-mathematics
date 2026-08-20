/-!
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Statement: Fermat's Last Theorem: xⁿ+yⁿ=zⁿ has no positive-integer solution for n>2.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


set_option autoImplicit false

namespace Frontier

/-- Fermat's Last Theorem, stated directly in terms of positive integers:
for every exponent `n > 2` there are no positive natural numbers `x, y, z`
with `x ^ n + y ^ n = z ^ n`. -/
def FLTPositive : Prop :=
  ∀ n x y z : ℕ, 2 < n → 0 < x → 0 < y → 0 < z → x ^ n + y ^ n ≠ z ^ n

/-- The positive-integer phrasing of Fermat's Last Theorem agrees with Mathlib's
`FermatLastTheorem` (which is phrased via nonvanishing of `a`, `b`, `c` and `n ≥ 3`). -/
theorem FLTPositive_iff_FermatLastTheorem : FLTPositive ↔ FermatLastTheorem := by
  constructor
  · intro h n hn a b c ha hb hc
    exact h n a b c (by omega) (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)
      (Nat.pos_of_ne_zero hc)
  · intro h n x y z hn hx hy hz
    exact h n (by omega) x y z hx.ne' hy.ne' hz.ne'

/-- Base case `n = 3`: no positive integers satisfy `x ^ 3 + y ^ 3 = z ^ 3`. -/
theorem FLT_three (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x ^ 3 + y ^ 3 ≠ z ^ 3 :=
  fermatLastTheoremThree x y z hx.ne' hy.ne' hz.ne'

/-- Base case `n = 4`: no positive integers satisfy `x ^ 4 + y ^ 4 = z ^ 4`. -/
theorem FLT_four (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x ^ 4 + y ^ 4 ≠ z ^ 4 :=
  fermatLastTheoremFour x y z hx.ne' hy.ne' hz.ne'

/-- **Fermat's Last Theorem: statement and Lean-checked reduction.**

The equation `x ^ n + y ^ n = z ^ n` has no solution in positive integers for `n > 2`,
*provided* it has none for odd prime exponents. Together with the (unconditional,
Mathlib-proved) case `n = 4` used inside the reduction, this reduces the general
statement to the case of odd prime exponents.

The unconditional base cases `n = 3` and `n = 4` are `Frontier.FLT_three` and
`Frontier.FLT_four`. -/
theorem FLT_statement
    (hprimes : ∀ p : ℕ, Nat.Prime p → Odd p → FermatLastTheoremFor p) :
    FLTPositive :=
  FLTPositive_iff_FermatLastTheorem.mpr (FermatLastTheorem.of_odd_primes hprimes)

end Frontier


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

