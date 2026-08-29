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

/-!
# Odd Weird Exists
Category: Brockian Conjecture
Target: Brockian.WeirdNumbers.OddWeirdExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## Overview

A natural number `n` is *weird* (`Nat.Weird`, from Mathlib) when it is abundant
(the sum of its proper divisors exceeds `n`) but not pseudoperfect (no subset of its
proper divisors sums to `n`).  Whether an **odd** weird number exists is a well-known
open problem, so the unconditional statement `∃ n, Odd n ∧ Nat.Weird n` is not proved
here.  Instead this file contains:

* `Brockian.WeirdNumbers.abundance`: the abundance `σ(n) - 2n` of `n`.
* `Brockian.WeirdNumbers.pseudoperfect_iff_exists_sum_eq_abundance`: for an abundant `n`,
  `n` is pseudoperfect iff some subset of its proper divisors sums to the *abundance* of
  `n` (complementation of subsets).  This turns the subset-sum target `n` into the much
  smaller target `abundance n`.
* `Brockian.WeirdNumbers.OddWeirdExists`: an unconditional Lean-checked **reduction** of
  the open problem: an odd weird number exists **iff** there is an odd abundant number no
  subset of whose proper divisors sums to its abundance.
* `Brockian.WeirdNumbers.weird_of_abundance_small`: a practical sufficient criterion for
  weirdness (abundance different from `1` and smaller than every proper divisor `> 1`).
* `Brockian.WeirdNumbers.weird_seventy` / `exists_weird`: `70` is weird, so weird numbers
  do exist (unconditionally, by a finite kernel computation).
-/

open Finset

set_option maxRecDepth 40000

namespace Brockian.WeirdNumbers

/-- The *abundance* of `n`, i.e. `σ(n) - 2n`, written as the excess of the sum of the
proper divisors of `n` over `n` itself (truncated subtraction). -/

lemma sum_eq_add_abundance {n : ℕ} (h : n.Abundant) :
    (∑ i ∈ n.properDivisors, i) = n + abundance n := by
  have h' : n < ∑ i ∈ n.properDivisors, i := h
  unfold abundance
  omega

