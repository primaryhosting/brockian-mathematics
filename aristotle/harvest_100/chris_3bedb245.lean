import Mathlib

-- NOTE: Lean 4 requires `import` lines to precede any doc comment, so the requested header
-- comment appears immediately after the single `import Mathlib` line.

/-!
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- Fermat's Last Theorem, stated in the "positive integers" form:
for every exponent `n > 2` there are no positive naturals `x, y, z` with `x ^ n + y ^ n = z ^ n`. -/
def FLT : Prop :=
  ∀ n x y z : ℕ, 2 < n → 0 < x → 0 < y → 0 < z → x ^ n + y ^ n ≠ z ^ n

/-- The positive-integer formulation `Frontier.FLT` agrees with Mathlib's `FermatLastTheorem`
(which is phrased with nonzero-ness hypotheses and `n ≥ 3`). -/
theorem FLT_iff_fermatLastTheorem : FLT ↔ FermatLastTheorem := by
  constructor
  · intro h n hn a b c ha hb hc
    exact h n a b c (by omega) (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)
      (Nat.pos_of_ne_zero hc)
  · intro h n x y z hn hx hy hz
    exact h n hn x y z hx.ne' hy.ne' hz.ne'

/-- Base case `n = 3` of Fermat's Last Theorem, in the positive-integer formulation. -/
theorem FLT_three (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x ^ 3 + y ^ 3 ≠ z ^ 3 :=
  fermatLastTheoremThree x y z hx.ne' hy.ne' hz.ne'

/-- Base case `n = 4` of Fermat's Last Theorem, in the positive-integer formulation. -/
theorem FLT_four (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x ^ 4 + y ^ 4 ≠ z ^ 4 :=
  fermatLastTheoremFour x y z hx.ne' hy.ne' hz.ne'

/-- **Fermat's Last Theorem: statement and Lean-checked reduction.**

The full statement `Frontier.FLT` — `x ^ n + y ^ n = z ^ n` has no solution in positive integers
for `n > 2` — follows from the special case of odd prime exponents `p ≥ 5`.

The remaining exponents are handled unconditionally here: every `n > 2` is divisible by `4` or by
an odd prime, the cases `n = 4` and `n = 3` being Mathlib's `fermatLastTheoremFour` and
`fermatLastTheoremThree`. -/
theorem FLT_statement
    (hp : ∀ p : ℕ, p.Prime → Odd p → 5 ≤ p → FermatLastTheoremFor p) : FLT := by
  rw [FLT_iff_fermatLastTheorem]
  intro n hn
  obtain hdvd | ⟨p, hpprime, hdvd, hpodd⟩ :=
    Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hn
  · exact FermatLastTheoremWith.mono hdvd fermatLastTheoremFour
  · rcases eq_or_lt_of_le hpprime.two_le with h2 | h2
    · exact absurd (h2 ▸ hpodd) (by decide)
    · rcases eq_or_lt_of_le (show 3 ≤ p by omega) with h3 | h3
      · exact FermatLastTheoremWith.mono hdvd (h3 ▸ fermatLastTheoremThree)
      · have h5 : 5 ≤ p := by
          obtain ⟨k, hk⟩ := hpodd
          omega
        exact FermatLastTheoremWith.mono hdvd (hp p hpprime hpodd h5)

end Frontier

import Mathlib

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

