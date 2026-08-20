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
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Whether there are infinitely many amicable numbers is an open problem.  What is proved here
is an unconditional formalisation of Thabit ibn Qurra's rule together with the resulting
*conditional reduction*: if there are infinitely many Thabit indices `k` (i.e. indices for
which `3·2^(k-1) - 1`, `3·2^k - 1` and `9·2^(2k-1) - 1` are all prime), then there are
infinitely many amicable numbers.
-/

namespace Brockian.AmicableNumbers

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- The sum of the proper divisors of `n` (the classical `s`-function). -/

lemma isAmicable_thabit {k : ℕ} (hk : ThabitIndex k) :
    IsAmicable (2 ^ k * (3 * 2 ^ (k - 1) - 1) * (3 * 2 ^ k - 1)) := by
  obtain ⟨hk2, hp, hq, hr⟩ := hk
  refine ⟨2 ^ k * (9 * 2 ^ (2 * k - 1) - 1), thabit_isAmicablePair hk2 hp hq hr ?_ ?_ ?_⟩
  · exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by positivity))
  · exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by positivity))
  · exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by positivity))

