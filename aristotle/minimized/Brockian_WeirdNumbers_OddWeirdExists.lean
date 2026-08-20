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
# Odd Weird Exists
Category: Brockian Conjecture
Target: Brockian.WeirdNumbers.OddWeirdExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

/-!
## Status

`OddWeirdExists` (the existence of an odd weird number) is an open problem, and is **not** proved
here. What is proved, axiom-cleanly:

* `oddWeirdExists_iff` — an elementary restatement of the target;
* `pseudoperfect_mul_left`, `pseudoperfect_of_dvd`, `not_pseudoperfect_of_dvd_of_weird` — every
  multiple of a pseudoperfect number is pseudoperfect, hence no divisor of a weird number is
  pseudoperfect;
* `not_dvd_945_of_weird`, `not_dvd_of_perfect_of_weird`, `not_perfect_of_weird` — concrete
  consequences (e.g. no weird number is a multiple of `945`, the smallest odd abundant number);
* `weird_mul_prime` — if `n` is weird and `p` is a prime exceeding the sum of the divisors of `n`,
  then `n * p` is weird;
* `oddWeirdExists_iff_infinite` — the conditional reduction: one odd weird number would already
  force infinitely many;
* `even_weird_exists` — the even case, via Mathlib's `Nat.weird_seventy`.

The relevant existing Mathlib material is `Mathlib/NumberTheory/FactorisationProperties.lean`
(`Nat.Abundant`, `Nat.Pseudoperfect`, `Nat.Weird`, `Nat.Abundant.of_dvd`, `Nat.weird_seventy`);
no Mathlib lemma closes the target itself.
-/

namespace Brockian.WeirdNumbers

/-- The Brockian statement "an odd weird number exists".

A natural number is *weird* (`Nat.Weird`, from Mathlib's
`Mathlib/NumberTheory/FactorisationProperties.lean`) when it is abundant (the sum of its proper
divisors exceeds it) but not pseudoperfect (no subset of its proper divisors sums to it).
Whether an odd weird number exists is an open problem; this file therefore develops
Lean-checked reductions and partial results around the statement. -/

def OddWeirdExists : Prop := ∃ n : ℕ, Odd n ∧ n.Weird

/-- Unfolding of `OddWeirdExists` into elementary arithmetic terms. -/
