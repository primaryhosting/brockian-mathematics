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

theorem dvd_factorial_pred_add_one_iff_prime {n : ℕ} (hn : 2 ≤ n) :
    n ∣ (n - 1)! + 1 ↔ Nat.Prime n := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [Nat.prime_iff_fac_equiv_neg_one (by omega : n ≠ 1)]
  constructor
  · intro h; linear_combination (norm := ring_nf) h
  · intro h; rw [h]; ring

/-- The "left half" of Clement's criterion: for odd `n ≥ 3`, `n` divides
`4 * ((n-1)! + 1) + n` if and only if `n` is prime. -/
