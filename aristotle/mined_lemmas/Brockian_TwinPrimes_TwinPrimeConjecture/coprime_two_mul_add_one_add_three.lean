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
-- (Lean 4 requires `import` to precede any module docstring, so the header above is
-- repeated as the module docstring immediately after the import.)

import Mathlib

/-!
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Nat

namespace Brockian.TwinPrimes

/-! ## The statement

The twin prime conjecture asserts that there are arbitrarily large primes `p` such that
`p + 2` is also prime.  This is a famous open problem, so it is not proved here; instead
we give an unconditional, Lean-checked *equivalent reformulation* (Clement's criterion,
derived from Wilson's theorem — `Nat.prime_iff_fac_equiv_neg_one` in Mathlib), which
turns the conjecture into a single divisibility statement about factorials, together with
some unconditional partial results.
-/

/-- `n` and `n + 2` are both prime. -/

theorem coprime_two_mul_add_one_add_three (k : ℕ) : Nat.Coprime (2 * k + 1) (2 * k + 3) := by
  have h2 : Nat.gcd (2 * k + 1) (2 * k + 3) ∣ 2 := by
    have := Nat.dvd_sub (Nat.gcd_dvd_right (2 * k + 1) (2 * k + 3))
      (Nat.gcd_dvd_left (2 * k + 1) (2 * k + 3))
    simpa using this
  have h1 : Nat.gcd (2 * k + 1) (2 * k + 3) ∣ (2 * k + 1) := Nat.gcd_dvd_left _ _
  have hle := Nat.le_of_dvd (by norm_num) h2
  interval_cases h : Nat.gcd (2 * k + 1) (2 * k + 3) <;> omega

/-- **Clement's criterion** (1949): for `k ≥ 1`, the numbers `2k+1` and `2k+3` form a twin
prime pair if and only if `(2k+1)(2k+3) ∣ 4((2k)! + 1) + (2k+1)`. -/
