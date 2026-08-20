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
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset

namespace Brockian.Equidistribution

/-- Triangular numbers: `T m = 1 + 2 + ⋯ + m = m (m+1) / 2`. -/

theorem tendsto_blk_atTop : Tendsto blk atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  refine ⟨T M, fun n hn => ?_⟩
  by_contra h
  have h1 : T (blk n + 1) ≤ T M := T_mono (by omega)
  have h2 := lt_T_blk_succ n
  omega

/-- **Existence of an equidistributed sequence.**  There is a sequence in `[0,1)` such that for
every subinterval `[a,b) ⊆ [0,1]` the asymptotic proportion of terms landing in `[a,b)` exists
and equals its length `b - a`. -/
