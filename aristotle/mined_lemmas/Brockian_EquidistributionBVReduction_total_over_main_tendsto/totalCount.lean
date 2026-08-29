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

def totalCount (q a N : ℕ) : ℕ := N.count (fun n => n ≡ a [MOD q])

/-- The *main term* predicted by equidistribution: a residue class mod `q` should
contain roughly a proportion `1 / q` of the integers below `N`. -/
