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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
## Practical numbers and practical twins

A positive integer `n` is *practical* if every `m ≤ σ(n)` is a sum of distinct divisors of `n`.
The *practical twin* problem asks whether there are infinitely many `n` such that both `n` and
`n + 2` are practical (this is a known but genuinely deep statement, proved by sieve methods;
no unconditional proof is formalised here).

This file develops:

* `IsPractical`, `DivisorComplete` and the equivalence `isPractical_iff_divisorComplete`
  between practicality and the elementary divisor-chain criterion "every divisor is at most one
  more than the sum of the smaller divisors";
* decidability of the criterion, and explicit practical twin pairs up to `(8190, 8192)`;
* `isPractical_two_pow`, `infinite_practical`: powers of two are practical, so there are
  infinitely many practical numbers;
* `isPractical_mul_prime`: the coprime case of Stewart's multiplication theorem, and the family
  `isPractical_prime_mul_two_pow`;
* `practicalTwinConjecture_iff` and `PracticalTwinInfinitude`: a Lean-checked reduction of the
  practical twin conjecture to the elementary criterion.
-/

set_option maxRecDepth 10000

open Finset

namespace Brockian.PracticalNumbers

/-- A positive integer `n` is *practical* if every `m ≤ σ(n)` is the sum of a set of
pairwise distinct divisors of `n`. -/

theorem practicalTwin_examples :
    PracticalTwin 2 ∧ PracticalTwin 4 ∧ PracticalTwin 6 ∧ PracticalTwin 16 ∧
      PracticalTwin 30 ∧ PracticalTwin 126 ∧ PracticalTwin 2046 ∧ PracticalTwin 8190 := by
  have key : ∀ n : ℕ, DivisorComplete n → DivisorComplete (n + 2) → PracticalTwin n := by
    intro n h1 h2
    exact ⟨(isPractical_iff_divisorComplete _).2 h1, (isPractical_iff_divisorComplete _).2 h2⟩
  refine ⟨key 2 (by decide) (by decide), key 4 (by decide) (by decide),
    key 6 (by decide) (by decide), key 16 (by decide) (by decide),
    key 30 (by decide) (by decide), key 126 (by decide) (by decide),
    key 2046 (by decide) (by decide), key 8190 (by decide) (by decide)⟩

/-- The Brockian "practical twin" conjecture: there are infinitely many `n` such that both
`n` and `n + 2` are practical. -/
