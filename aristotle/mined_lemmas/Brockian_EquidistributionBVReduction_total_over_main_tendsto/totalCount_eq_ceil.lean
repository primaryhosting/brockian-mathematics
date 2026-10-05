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
# Total Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.total_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open Filter Topology

namespace Brockian.EquidistributionBVReduction

/-- The *total* count: the number of natural numbers `n < N` that lie in the
residue class `a` modulo `q`. -/

lemma totalCount_eq_ceil (q a N : ℕ) (hq : 0 < q) :
    ((totalCount q a N : ℤ)) = ⌈((N : ℚ) - ((a % q : ℕ) : ℚ)) / (q : ℚ)⌉ :=
  Nat.count_modEq_card_eq_ceil N hq a

/-- The total count differs from the main term by at most `1`: two-sided integer bounds. -/
