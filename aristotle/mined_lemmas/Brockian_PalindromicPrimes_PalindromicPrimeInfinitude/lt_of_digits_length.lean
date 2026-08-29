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
# Palindromic Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.PalindromicPrimes.PalindromicPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring `/-! ... -/`, so the header above
-- is given as a plain block comment and repeated as the module docstring below.)

import Mathlib

/-!
# Palindromic Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.PalindromicPrimes.PalindromicPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PalindromicPrimes

/-- `n` is a palindrome in base `b`: its list of base-`b` digits is its own reverse. -/

theorem lt_of_digits_length {n : ℕ} (hn : n ≠ 0) : (Nat.digits 10 n).length < 10 * n := by
  have h1 : (10 : ℕ) ^ (Nat.digits 10 n).length ≤ 10 * n :=
    Nat.base_pow_length_digits_le 10 n (by norm_num) hn
  have h2 : (Nat.digits 10 n).length < 10 ^ (Nat.digits 10 n).length :=
    Nat.lt_pow_self (by norm_num)
  omega

/-- **Palindromic Prime Infinitude (conditional reduction).**

The unconditional infinitude of base-ten palindromic primes is an open problem.  What is
proved here is a reduction: if palindromic primes with arbitrarily many digits exist, then
there are infinitely many palindromic primes. -/
