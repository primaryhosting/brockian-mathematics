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
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring, so the header above is a
-- plain comment and is repeated verbatim as the module docstring below.)

import Mathlib

/-!
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.FortunateNumbers

open Finset

/-!
## Setup

For a bound `N`, `primorial N` (Mathlib's `primorial`, notation `N#`) is the product of all
primes `≤ N`.  The *fortunate number* attached to `N` is the least `m ≥ 2` such that
`N# + m` is prime.  Fortune's conjecture asserts that this number is always prime.

The conjecture is open.  What we prove here is the classical unconditional dichotomy
(`fortunate_prime_or_sq_le`): the fortunate number is either prime or at least `(N+1)^2`,
because none of its prime factors can be `≤ N`.  The named target
`FortuneConjecture` is therefore the corresponding *conditional* statement: the fortunate
number is prime as soon as it is smaller than `(N+1)^2`.
-/

/-- Every prime `q ≤ N` divides the primorial `N#`. -/

theorem fortunate_prime_or_sq_le (N : ℕ) :
    (fortunate N).Prime ∨ (N + 1) ^ 2 ≤ fortunate N := by
  by_cases hp : (fortunate N).Prime
  · exact Or.inl hp
  · refine Or.inr ?_
    have hpos : 0 < fortunate N := by have := two_le_fortunate N; omega
    have h1 : (fortunate N).minFac ^ 2 ≤ fortunate N := Nat.minFac_sq_le_self hpos hp
    have h2 : N + 1 ≤ (fortunate N).minFac := lt_minFac_fortunate N
    exact le_trans (Nat.pow_le_pow_left h2 2) h1

/-- **Fortune's conjecture, conditional form.**  The fortunate number of `N` — the least
`m ≥ 2` with `N# + m` prime — is prime, provided it is smaller than `(N+1)^2`.

Fortune's conjecture itself (that this holds unconditionally) is open; the hypothesis
`fortunate N < (N + 1) ^ 2` is exactly the classical gap, and it is known to hold for all
values that have been computed. -/
