/-
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- The elementary statement of Fermat's Last Theorem: for every exponent `n ≥ 3`,
the equation `x ^ n + y ^ n = z ^ n` has no solution in positive integers. -/
def FLTStatement : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → x ^ n + y ^ n ≠ z ^ n

/-- The elementary formulation `Frontier.FLTStatement` agrees with Mathlib's
`FermatLastTheorem`. -/
theorem FLTStatement_iff_fermatLastTheorem : FLTStatement ↔ FermatLastTheorem := by
  constructor
  · intro h n hn a b c ha hb hc
    exact h n hn a b c (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb) (Nat.pos_of_ne_zero hc)
  · intro h n hn x y z hx hy hz
    exact h n hn x y z hx.ne' hy.ne' hz.ne'

/-- The elementary statement of Fermat's Last Theorem for a fixed exponent `n`. -/
def FLTStatementFor (n : ℕ) : Prop :=
  ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → x ^ n + y ^ n ≠ z ^ n

theorem FLTStatementFor_iff_fermatLastTheoremFor (n : ℕ) :
    FLTStatementFor n ↔ FermatLastTheoremFor n := by
  constructor
  · intro h a b c ha hb hc
    exact h a b c (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb) (Nat.pos_of_ne_zero hc)
  · intro h x y z hx hy hz
    exact h x y z hx.ne' hy.ne' hz.ne'

/-- Base case `n = 3`: `x ³ + y ³ = z ³` has no positive-integer solution. -/
theorem FLT_statement_three : FLTStatementFor 3 :=
  (FLTStatementFor_iff_fermatLastTheoremFor 3).2 fermatLastTheoremThree

/-- Base case `n = 4` (Fermat's own descent argument):
`x ⁴ + y ⁴ = z ⁴` has no positive-integer solution. -/
theorem FLT_statement_four : FLTStatementFor 4 :=
  (FLTStatementFor_iff_fermatLastTheoremFor 4).2 fermatLastTheoremFour

/-- **Lean-checked reduction of Fermat's Last Theorem to odd prime exponents.**

The full statement of Fermat's Last Theorem — no positive integers `x, y, z` satisfy
`x ^ n + y ^ n = z ^ n` for any exponent `n ≥ 3` — is *equivalent* to its special case
for odd prime exponents.  The nontrivial direction combines the case `n = 4`
(Fermat's descent) with the fact that every `n > 2` is divisible by `4` or by an odd prime. -/
theorem FLT_statement :
    FLTStatement ↔ ∀ p : ℕ, p.Prime → Odd p → FLTStatementFor p := by
  rw [FLTStatement_iff_fermatLastTheorem]
  constructor
  · intro h p hp hodd
    refine (FLTStatementFor_iff_fermatLastTheoremFor p).2 (h p ?_)
    have hp2 : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hodd
    exact hp.two_le.lt_of_ne (Ne.symm hp2)
  · intro h
    exact FermatLastTheorem.of_odd_primes fun p hp hodd =>
      (FLTStatementFor_iff_fermatLastTheoremFor p).1 (h p hp hodd)

end Frontier

#print axioms Frontier.FLT_statement
#print axioms Frontier.FLT_statement_three
#print axioms Frontier.FLT_statement_four

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

