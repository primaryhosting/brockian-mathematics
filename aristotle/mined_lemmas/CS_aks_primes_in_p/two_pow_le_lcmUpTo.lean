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

import RequestProject.AKS.Algorithm

/-!
# Correctness of the AKS primality test

The main result of this file is `AKS.aksTest_iff_prime`:
the decision procedure `AKS.aksTest` returns `true` exactly on the primes.
-/

namespace AKS

open Polynomial Finset


theorem two_pow_le_lcmUpTo (M : ℕ) : 2 ^ M ≤ lcmUpTo (2 * M) := by
  refine le_trans (AKS.two_pow_le_choose M) ?_
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (lcmUpTo_ne_zero _)) (choose_dvd_lcmUpTo M)

/-- There is a small `r ≥ 2` for which `n` has multiplicative order greater than `K`
modulo `r` (expressed as: no power `n ^ i` with `1 ≤ i ≤ K` is `1` modulo `r`). -/
