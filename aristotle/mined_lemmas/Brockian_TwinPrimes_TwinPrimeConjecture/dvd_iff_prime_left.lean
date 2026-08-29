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

/-
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a `/-! ... -/` module docstring,
-- since Lean 4 requires `import` commands to precede every other command, docstrings included.)

import Mathlib

open scoped Nat

namespace Brockian.TwinPrimes

/-- The **Twin Prime Conjecture**: there are arbitrarily large primes `p` such that
`p + 2` is also prime.

This statement is a famous open problem, so it is recorded here as a `Prop`-valued
definition; the theorems below give Lean-checked equivalent reformulations of it. -/

theorem dvd_iff_prime_left {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) :
    n ∣ 4 * ((n - 1)! + 1) + n ↔ Nat.Prime n := by
  have h4 : Nat.Coprime n 4 := coprime_four_of_odd hodd
  rw [Nat.dvd_add_self_right]
  rw [show (4 : ℕ) * ((n - 1)! + 1) = ((n - 1)! + 1) * 4 by ring]
  constructor
  · intro h
    exact (dvd_factorial_pred_add_one_iff_prime (by omega)).mp (h4.dvd_of_dvd_mul_right h)
  · intro h
    exact Dvd.dvd.mul_right ((dvd_factorial_pred_add_one_iff_prime (by omega)).mpr h) 4

/-- A Wilson-type criterion for `n + 2`: for `n ≥ 3`, `n + 2` divides `2 * (n-1)! + 1`
if and only if `n + 2` is prime. -/
