/-
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- Fermat's Last Theorem for the exponent `n`, stated directly in terms of positive
integers: there are no positive naturals `x, y, z` with `x ^ n + y ^ n = z ^ n`. -/
def FLTFor (n : ℕ) : Prop :=
  ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → x ^ n + y ^ n ≠ z ^ n

/-- The positivity formulation `FLTFor` agrees with Mathlib's `FermatLastTheoremFor`. -/
theorem FLTFor_iff_fermatLastTheoremFor (n : ℕ) :
    FLTFor n ↔ FermatLastTheoremFor n := by
  constructor
  · intro h x y z hx hy hz
    exact h x y z (Nat.pos_of_ne_zero hx) (Nat.pos_of_ne_zero hy) (Nat.pos_of_ne_zero hz)
  · intro h x y z hx hy hz
    exact h x y z hx.ne' hy.ne' hz.ne'

/-- Base case `n = 3` (Euler): `x ^ 3 + y ^ 3 = z ^ 3` has no positive solutions. -/
theorem FLTFor_three : FLTFor 3 :=
  (FLTFor_iff_fermatLastTheoremFor 3).2 fermatLastTheoremThree

/-- Base case `n = 4` (Fermat): `x ^ 4 + y ^ 4 = z ^ 4` has no positive solutions. -/
theorem FLTFor_four : FLTFor 4 :=
  (FLTFor_iff_fermatLastTheoremFor 4).2 fermatLastTheoremFour

/-- Any exponent that is a multiple of an exponent for which FLT holds also satisfies FLT. -/
theorem FLTFor_of_dvd {m n : ℕ} (hmn : m ∣ n) (hm : FLTFor m) : FLTFor n :=
  (FLTFor_iff_fermatLastTheoremFor n).2
    (((FLTFor_iff_fermatLastTheoremFor m).1 hm).mono hmn)

/-- **Fermat's Last Theorem, reduced to odd prime exponents `p ≥ 5`.**

The statement of Fermat's Last Theorem is: for every exponent `n > 2` there are no positive
integers `x, y, z` with `x ^ n + y ^ n = z ^ n`.  Here it is proved from the special case of
odd prime exponents `p ≥ 5`; the remaining exponents are handled unconditionally, using the
classical base cases `n = 4` (Fermat) and `n = 3` (Euler), both available in Mathlib. -/
theorem FLT_statement
    (hodd : ∀ p : ℕ, p.Prime → Odd p → 5 ≤ p → FLTFor p) :
    ∀ n : ℕ, 2 < n → FLTFor n := by
  have key : FermatLastTheorem := by
    refine FermatLastTheorem.of_odd_primes ?_
    intro p hp hpodd
    rcases eq_or_lt_of_le hp.two_le with h2 | h2
    · exact absurd (h2 ▸ hpodd) (by decide)
    · rcases eq_or_lt_of_le (Nat.succ_le_of_lt h2) with h3 | h3
      · exact h3 ▸ fermatLastTheoremThree
      · have h5 : 5 ≤ p := by
          rcases hpodd with ⟨k, hk⟩
          omega
        exact (FLTFor_iff_fermatLastTheoremFor p).1 (hodd p hp hpodd h5)
  intro n hn
  exact (FLTFor_iff_fermatLastTheoremFor n).2 (key n hn)

end Frontier

