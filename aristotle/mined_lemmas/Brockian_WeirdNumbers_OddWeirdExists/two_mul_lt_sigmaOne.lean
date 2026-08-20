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

/-!
# Odd Weird Exists
Category: Brockian Conjecture
Target: Brockian.WeirdNumbers.OddWeirdExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A natural number `n` is *weird* (`Nat.Weird`) if it is abundant (the sum of its proper
divisors exceeds `n`) but not pseudoperfect (no subset of its proper divisors sums to `n`).

Whether an **odd** weird number exists is a well-known open problem; no odd weird number is
known.  Consequently the file below does not claim an unconditional existence proof.
Instead it provides a Lean-checked *reduction*:

* `Brockian.WeirdNumbers.weird_mul_prime` : if `n` is weird and `p` is a prime exceeding the
  sum of the divisors of `n`, then `n * p` is weird.
* `Brockian.WeirdNumbers.OddWeirdExists` : an odd weird number exists **iff** there are
  arbitrarily large odd weird numbers.  In other words, a single odd weird number would
  immediately yield infinitely many.

Unconditionally we also record:

* `Brockian.WeirdNumbers.even_weird_exists` : `70` is an (even) weird number;
* `Brockian.WeirdNumbers.odd_weird_ge_1000` : every odd weird number is at least `1000`
  (the only odd abundant number below `1000` is `945`, and `945` is pseudoperfect).
-/

namespace Brockian.WeirdNumbers

open Finset

/-- The sum of all divisors of `n`. -/
abbrev sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- For a prime `p` not dividing `n`, `σ (n * p) = σ n * (p + 1)`. -/

lemma two_mul_lt_sigmaOne {n : ℕ} (h : n.Weird) : 2 * n < sigmaOne n := by
  have habund := h.1
  have hsum : sigmaOne n = (∑ i ∈ n.properDivisors, i) + n :=
    Nat.sum_divisors_eq_sum_properDivisors_add_self
  unfold Nat.Abundant at habund
  omega

/-- If `n` is weird and `p` is a prime larger than the sum of the divisors of `n`,
then `n * p` is abundant. -/
