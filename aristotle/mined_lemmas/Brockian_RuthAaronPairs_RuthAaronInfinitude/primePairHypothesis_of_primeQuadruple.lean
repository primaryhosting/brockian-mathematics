import Brockian.RuthAaronPairs

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

import Mathlib

/-!
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A *Ruth–Aaron pair* is a pair of consecutive integers `(n, n+1)` with the same sum of prime
factors counted with multiplicity, e.g. `(714, 715)`: `714 = 2·3·7·17`, `715 = 5·11·13`, and
`2 + 3 + 7 + 17 = 29 = 5 + 11 + 13`.  Whether there are infinitely many such pairs is a
well-known open problem (Erdős).

This file contains:

* a definition of `sopfr` (sum of prime factors with multiplicity) and of `IsRuthAaron`;
* unconditional verifications that `5, 8, 77, 714` are Ruth–Aaron numbers;
* an unconditional *construction*: `isRuthAaron_of_prime_pair`, producing a Ruth–Aaron pair out
  of any `B ≥ 2` for which the two integers `B·d − 1` and `(B+1)·d − 1` are prime, where
  `d = sopfr (B+1) − sopfr B > 0`;
* the resulting conditional infinitude theorem `RuthAaronInfinitude`, and a further reduction
  `ruthAaronInfinitude_of_primeQuadruple` of the required hypothesis to a Schinzel Hypothesis H
  statement for one explicit quadruple of polynomials.

So the deliverable is a Lean-checked *conditional reduction*: Ruth–Aaron infinitude follows from
a prime `k`-tuple conjecture, not from anything Ruth–Aaron specific.
-/

namespace Brockian.RuthAaronPairs

/-- `sopfr n` is the sum of the prime factors of `n`, counted with multiplicity
(`sopfr 0 = sopfr 1 = 0`). -/

theorem primePairHypothesis_of_primeQuadruple (H : PrimeQuadrupleHypothesis) :
    PrimePairHypothesis := by
  intro N
  obtain ⟨t, htN, ht, ht1, hp, hq⟩ := H (N + 2)
  have ht2 : 2 ≤ t := ht.two_le
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
  have hsq : (s + 2) ^ 2 = s ^ 2 + 4 * s + 4 := by ring
  have hd : 3 * (s + 2) - 3 = 3 * s + 3 := by omega
  have e1 : 4 * (s + 2) * (3 * s + 3) = 12 * s ^ 2 + 36 * s + 24 := by ring
  have e2 : (4 * (s + 2) + 1) * (3 * s + 3) = 12 * s ^ 2 + 39 * s + 27 := by ring
  refine ⟨4 * (s + 2), 3 * (s + 2) - 3, by omega, by omega, ?_, ?_, ?_⟩
  · rw [sopfr_four_mul ht, sopfr_prime ht1]
    omega
  · have h : 4 * (s + 2) * (3 * (s + 2) - 3) - 1
        = 12 * (s + 2) ^ 2 - 12 * (s + 2) - 1 := by
      rw [hd, e1, hsq]; omega
    rwa [h]
  · have h : (4 * (s + 2) + 1) * (3 * (s + 2) - 3) - 1
        = 12 * (s + 2) ^ 2 - 9 * (s + 2) - 4 := by
      rw [hd, e2, hsq]; omega
    rwa [h]

/-- **Ruth–Aaron infinitude from Hypothesis H for an explicit quadruple.** -/
