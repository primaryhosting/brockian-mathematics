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

theorem dvd_iff_prime_right {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) :
    (n + 2) ∣ 4 * ((n - 1)! + 1) + n ↔ Nat.Prime (n + 2) := by
  have hodd2 : Odd (n + 2) := by rcases hodd with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
  have h2 : Nat.Coprime (n + 2) 2 := Nat.coprime_two_right.mpr hodd2
  rw [show 4 * ((n - 1)! + 1) + n = (2 * (n - 1)! + 1) * 2 + (n + 2) by ring,
    Nat.dvd_add_self_right]
  constructor
  · intro h
    exact (dvd_two_mul_factorial_add_one_iff_prime hn).mp (h2.dvd_of_dvd_mul_right h)
  · intro h
    exact Dvd.dvd.mul_right ((dvd_two_mul_factorial_add_one_iff_prime hn).mpr h) 2

/-! ### Clement's criterion and reformulations of the conjecture -/

/-- **Clement's criterion** for twin primes: for odd `n ≥ 3`, the pair `(n, n+2)` is a twin
prime pair if and only if `n * (n + 2)` divides `4 * ((n-1)! + 1) + n`. -/
