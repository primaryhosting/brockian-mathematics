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
## Overview

A natural number `n` is *weird* when it is abundant (the sum of its proper divisors exceeds
`n`) but not semiperfect (no set of distinct proper divisors of `n` sums to `n`).  The smallest
weird number is `70`.

Whether an **odd** weird number exists is a well-known open problem; none is known, and none
exists below very large search bounds.  Accordingly, the target statement
`Brockian.WeirdNumbers.OddWeirdExists` is formalised here as a *conditional reduction*: it derives
the existence of an odd weird number from the existence of an odd abundant number whose
*abundance* `σ(n) - 2n` is not a subset sum of the proper divisors of `n`.

The reduction is not a weakening: `weird_iff_abundance_not_representable` shows that the
hypothesis is in fact equivalent to the conclusion's content, and it is the numerically more
convenient criterion (the abundance is usually far smaller than `n`).

Besides that, this file contains:

* `isWeird_70` — a machine-checked verification that `70` is weird (a sanity check on the
  definitions);
* `no_odd_weird_below_1000` — no odd weird number is smaller than `1000`;
* `isWeird_mul_prime` — if `n` is weird and `p` is a prime larger than `σ n`, then `n * p` is
  weird; hence (`infinite_odd_weird_of_odd_weird`) a single odd weird number would produce
  infinitely many.
-/

namespace Brockian.WeirdNumbers

open Finset

/-- `n` is *semiperfect* (pseudoperfect) if some set of distinct proper divisors of `n`
sums to `n`. -/

theorem infinite_odd_weird_of_odd_weird (h : ∃ n, Odd n ∧ IsWeird n) :
    ∀ N : ℕ, ∃ m > N, Odd m ∧ IsWeird m := by
  obtain ⟨n, hodd, hw⟩ := h
  intro N
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd hw.1 (by decide)
    · exact h
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (max ((∑ d ∈ n.divisors, d) + 1) (N + 1))
  have hpσ : ∑ d ∈ n.divisors, d < p := lt_of_lt_of_le (by omega) (le_trans (le_max_left _ _) hple)
  have hpN : N < p := lt_of_lt_of_le (by omega) (le_trans (le_max_right _ _) hple)
  have hpodd : Odd p := hp.odd_of_ne_two (by
    intro h2
    have : (2 : ℕ) ≤ ∑ d ∈ n.divisors, d := by
      have h1 : n ≤ ∑ d ∈ n.divisors, d :=
        Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i)
          (Nat.mem_divisors_self n hn.ne')
      have hab : n < ∑ d ∈ n.properDivisors, d := hw.1
      have := sum_properDivisors_eq n hn
      omega
    omega)
  refine ⟨n * p, ?_, hodd.mul hpodd, isWeird_mul_prime n p hn hp hpσ hw⟩
  calc N < p := hpN
    _ ≤ n * p := Nat.le_mul_of_pos_left p hn

end Brockian.WeirdNumbers

