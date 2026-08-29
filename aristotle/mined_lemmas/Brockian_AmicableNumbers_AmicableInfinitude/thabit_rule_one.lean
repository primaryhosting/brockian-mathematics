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
-/

namespace Brockian.AmicableNumbers

open Finset

/-- The sum of the proper divisors of `n` (all divisors of `n` other than `n` itself). -/

theorem thabit_rule_one : IsAmicablePair 220 284 := by
  have h : ThabitTriple 1 := ⟨le_refl 1, by norm_num, by norm_num, by norm_num⟩
  have := thabit_rule h
  norm_num at this
  exact this

/-! ## The conditional infinitude statement -/

/-- **Conditional infinitude of amicable numbers.**  If Thabit's condition holds for
infinitely many `k` (i.e. for arbitrarily large `k` the three Thabit numbers are all prime),
then there are infinitely many amicable numbers. -/
