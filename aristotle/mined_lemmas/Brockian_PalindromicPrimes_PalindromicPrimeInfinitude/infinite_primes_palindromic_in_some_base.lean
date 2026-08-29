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

theorem infinite_primes_palindromic_in_some_base :
    {p : ℕ | Nat.Prime p ∧ ∃ b, 1 < b ∧ IsPalindromic b p}.Infinite := by
  apply Nat.infinite_setOf_prime.mono
  intro p hp
  refine ⟨hp, p + 1, hp.one_lt.trans (Nat.lt_succ_self p), ?_⟩
  have : Nat.digits (p + 1) p = [p] := Nat.digits_of_lt (p + 1) p hp.ne_zero (Nat.lt_succ_self p)
  simp [IsPalindromic, this]

/-! ## The conditional reduction -/

/-- A crude bound turning "many digits" into "large": a nonzero `n` has fewer than `10 * n`
base-ten digits. -/
