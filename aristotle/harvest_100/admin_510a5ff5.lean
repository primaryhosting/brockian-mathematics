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

namespace Frontier

/-- Fermat's Last Theorem for a fixed exponent `n`, stated with positive integers:
`x ^ n + y ^ n = z ^ n` has no solution with `x, y, z > 0`. -/
def FLTFor (n : ℕ) : Prop :=
  ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → x ^ n + y ^ n ≠ z ^ n

/-- Fermat's Last Theorem: for every exponent `n > 2`, the equation `x ^ n + y ^ n = z ^ n`
has no solution in positive integers. -/
def FLT : Prop := ∀ n : ℕ, 2 < n → FLTFor n

/-- The positivity form `FLTFor n` agrees with Mathlib's `FermatLastTheoremFor n`
(which is phrased with `≠ 0`). -/
theorem FLTFor_iff_fermatLastTheoremFor (n : ℕ) : FLTFor n ↔ FermatLastTheoremFor n := by
  constructor
  · intro h x y z hx hy hz
    exact h x y z (Nat.pos_of_ne_zero hx) (Nat.pos_of_ne_zero hy) (Nat.pos_of_ne_zero hz)
  · intro h x y z hx hy hz
    exact h x y z hx.ne' hy.ne' hz.ne'

/-- `FLT` agrees with Mathlib's `FermatLastTheorem`. -/
theorem FLT_iff_fermatLastTheorem : FLT ↔ FermatLastTheorem := by
  constructor
  · intro h n hn
    exact (FLTFor_iff_fermatLastTheoremFor n).1 (h n (by omega))
  · intro h n hn
    exact (FLTFor_iff_fermatLastTheoremFor n).2 (h n (by omega))

/-- Base case `n = 3` (Euler): from Mathlib's `fermatLastTheoremThree`. -/
theorem FLT_three : FLTFor 3 :=
  (FLTFor_iff_fermatLastTheoremFor 3).2 fermatLastTheoremThree

/-- Base case `n = 4` (Fermat's descent): from Mathlib's `fermatLastTheoremFour`. -/
theorem FLT_four : FLTFor 4 :=
  (FLTFor_iff_fermatLastTheoremFor 4).2 fermatLastTheoremFour

/-- Multiplicativity of the statement in the exponent: if `m ∣ n` and FLT holds for `m`,
then it holds for `n`. -/
theorem FLT_mono {m n : ℕ} (hmn : m ∣ n) (hm : FLTFor m) : FLTFor n :=
  (FLTFor_iff_fermatLastTheoremFor n).2
    (((FLTFor_iff_fermatLastTheoremFor m).1 hm).mono hmn)

/-- **Formal statement of Fermat's Last Theorem, together with a Lean-checked reduction
to the case of odd prime exponents.**

`x ^ n + y ^ n = z ^ n` has no positive-integer solution for `n > 2` **if and only if** it has
no positive-integer solution for every odd prime exponent `p`.

The nontrivial (←) direction is the classical reduction: every `n > 2` is divisible by `4` or by
an odd prime, and the case `n = 4` is Fermat's descent
(Mathlib's `FermatLastTheorem.of_odd_primes` and `fermatLastTheoremFour`). -/
theorem FLT_statement :
    FLT ↔ ∀ p : ℕ, p.Prime → Odd p → FLTFor p := by
  constructor
  · intro h p hp hodd
    exact h p (lt_of_le_of_ne hp.two_le (by rintro rfl; simp [Nat.odd_iff] at hodd))
  · intro h
    refine FLT_iff_fermatLastTheorem.2 (FermatLastTheorem.of_odd_primes ?_)
    intro p hp hodd
    exact (FLTFor_iff_fermatLastTheoremFor p).1 (h p hp hodd)

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

