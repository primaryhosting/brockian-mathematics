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

lemma isRuthAaron_seventySeven : IsRuthAaron 77 :=
  ⟨by norm_num, by rw [sopfr_seventySeven]; exact sopfr_seventyEight.symm⟩

/-- `(714, 715)` is the original Ruth–Aaron pair. -/
