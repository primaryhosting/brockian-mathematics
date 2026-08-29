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
# Gilbreath Conjecture
Category: Brockian Conjecture
Target: Brockian.GilbreathConjecture.GilbreathConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring `/-! ... -/`, so the
-- required header above is written as an ordinary block comment.)

import Mathlib

/-!
## Overview

Gilbreath's conjecture concerns the *Gilbreath array* built from the primes: the
zeroth row is the sequence of primes `2, 3, 5, 7, 11, ...` and each subsequent row is
the sequence of absolute differences of consecutive entries of the previous row.  The
conjecture asserts that every row after the zeroth one begins with `1`.

The conjecture is open.  This file develops the standard finite-certificate reduction
(the argument underlying Odlyzko's numerical verification):

* `GoodRow k m` says that row `k` begins with `1` and its next `m` entries all lie in
  `{0, 2}`.  This is a *finite* condition.
* `gil_head_eq_one_of_goodRow`: a single certificate `GoodRow k m` proves that each of
  the `m + 1` rows `k, k+1, …, k+m` begins with `1`.
* `GilbreathConjecture`: if such certificates exist covering every row
  (`OdlyzkoCriterion`), then the Gilbreath conjecture holds.
* `odlyzkoCriterion_iff_gilbreathProperty`: the criterion is in fact equivalent to the
  conjecture, so this is a genuine reduction and not a strengthening.
* Finally we verify the certificate `GoodRow 5 24` unconditionally, which yields the
  unconditional partial result that rows `1` through `29` all begin with `1`.
-/

namespace Brockian.GilbreathConjecture

/-- `gil k n` is the `n`-th entry (`0`-indexed) of the `k`-th row of the Gilbreath
array: row `0` is the sequence of primes, and each later row consists of the absolute
differences of consecutive entries of the previous row. -/

private lemma gp28 : gil 0 28 = 109 := nth_prime_of_count (by norm_num) (by decide)
