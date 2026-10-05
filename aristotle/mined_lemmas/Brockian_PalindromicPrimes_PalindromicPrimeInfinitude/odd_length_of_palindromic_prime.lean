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

(Note: Lean 4 requires `import` commands to precede every other command, including
module docstrings, so the header above is a plain block comment `/- ... -/`; the same
text is repeated as the module docstring `/-! ... -/` immediately after the import.)
-/

import Mathlib

/-!
# Palindromic Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.PalindromicPrimes.PalindromicPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PalindromicPrimes

open Nat

/-- `IsPalindromic b n` says that the base-`b` digit expansion of `n` reads the same
forwards and backwards. -/

theorem odd_length_of_palindromic_prime {p : ℕ} (hp : p.Prime) (hpal : IsPalindromic 10 p)
    (hne : p ≠ 11) : Odd (Nat.digits 10 p).length := by
  rw [Nat.odd_iff, ← Nat.not_even_iff]
  intro he
  exact hne ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).1
    (eleven_dvd_of_palindromic_even_length hpal he)).symm

/-- **Palindromic prime infinitude, reduced to a digit-length statement.**

The set of base-10 palindromic primes is infinite if and only if, for every `k`, there is a
palindromic prime with more than `k` decimal digits — and such a prime automatically has an
*odd* number of digits, since every even-length palindrome is divisible by `11`.

(The infinitude of base-10 palindromic primes is an open problem; this is a Lean-checked
equivalence, not a proof of either side.) -/
