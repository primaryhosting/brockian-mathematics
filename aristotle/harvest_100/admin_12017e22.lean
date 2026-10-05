-- (Lean 4 requires `import` lines to precede any module docstring, so the required
-- header comment appears immediately below the import.)
import Mathlib

/-!
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

/-- Fermat's Last Theorem for a fixed exponent `n`, stated with *positive* integers:
there are no `x, y, z > 0` with `x ^ n + y ^ n = z ^ n`. -/
def FLTFor (n : ℕ) : Prop := ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → x ^ n + y ^ n ≠ z ^ n

/-- Fermat's Last Theorem: for every exponent `n > 2` the equation `x ^ n + y ^ n = z ^ n`
has no solution in positive integers. -/
def FLT : Prop := ∀ n : ℕ, 2 < n → FLTFor n

/-- The positive-integer formulation for a fixed exponent agrees with Mathlib's
`FermatLastTheoremFor` (which phrases the same thing via nonvanishing). -/
theorem FLTFor_iff_fermatLastTheoremFor (n : ℕ) : FLTFor n ↔ FermatLastTheoremFor n := by
  constructor
  · intro h a b c ha hb hc
    exact h a b c (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb) (Nat.pos_of_ne_zero hc)
  · intro h x y z hx hy hz
    exact h x y z hx.ne' hy.ne' hz.ne'

/-- The positive-integer formulation of Fermat's Last Theorem agrees with Mathlib's
`FermatLastTheorem`. -/
theorem FLT_iff_fermatLastTheorem : FLT ↔ FermatLastTheorem := by
  constructor
  · intro h n hn
    exact (FLTFor_iff_fermatLastTheoremFor n).1 (h n (by omega))
  · intro h n hn
    exact (FLTFor_iff_fermatLastTheoremFor n).2 (h n (by omega))

/-- If `FLTFor` holds for an exponent `m`, it holds for every multiple of `m`. -/
theorem FLTFor_of_dvd {m n : ℕ} (hmn : m ∣ n) (hm : FLTFor m) : FLTFor n :=
  (FLTFor_iff_fermatLastTheoremFor n).2 <|
    FermatLastTheoremFor.mono hmn ((FLTFor_iff_fermatLastTheoremFor m).1 hm)

/-- Base case `n = 3`: `x ^ 3 + y ^ 3 = z ^ 3` has no positive solution. -/
theorem FLT_three : FLTFor 3 := (FLTFor_iff_fermatLastTheoremFor 3).2 fermatLastTheoremThree

/-- Base case `n = 4`: `x ^ 4 + y ^ 4 = z ^ 4` has no positive solution. -/
theorem FLT_four : FLTFor 4 := (FLTFor_iff_fermatLastTheoremFor 4).2 fermatLastTheoremFour

/-- **Fermat's Last Theorem: statement and reduction to prime exponents `p ≥ 5`.**

The equation `x ^ n + y ^ n = z ^ n` has no solution in positive integers for any `n > 2`,
provided it has none for prime exponents `p ≥ 5`.

The exponents `n = 3` and `n = 4` (and hence all their multiples) are handled unconditionally
here, using the classical proofs of those two cases; every remaining exponent `n > 2` is
divisible by `4` or by an odd prime, and an odd prime other than `3` is at least `5`. -/
theorem FLT_statement (hprimes : ∀ p : ℕ, p.Prime → 5 ≤ p → FLTFor p) : FLT := by
  intro n hn
  obtain hdvd | ⟨p, hp, hdvd, hpodd⟩ :=
    Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hn
  · exact FLTFor_of_dvd hdvd FLT_four
  · refine FLTFor_of_dvd hdvd ?_
    rcases eq_or_ne p 3 with rfl | hp3
    · exact FLT_three
    · refine hprimes p hp ?_
      have h2 := hp.two_le
      rcases hpodd with ⟨k, hk⟩
      omega

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

