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
# Config Count Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology

namespace Brockian.EquidistributionBVReduction

/-- The number of "configurations" below `N` in the arithmetic progression
`a mod q`, i.e. the cardinality of `{n < N | n ≡ a [MOD q]}`. -/

theorem configCount_eq (q a N : ℕ) (hq : 0 < q) :
    configCount q a N = N / q + (if a % q < N % q then 1 else 0) := by
  have h : configCount q a N = Nat.count (fun x => x ≡ a [MOD q]) N := by
    rw [Nat.count_eq_card_filter_range]
    rfl
  rw [h, Nat.count_modEq_card N hq a]

/-- Two-sided bound: `q * configCount q a N` differs from `N` by at most `q`. -/
