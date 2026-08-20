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
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Brockian.Equidistribution

/-- A sequence `u : ℕ → ℝ` is *asymptotically equidistributed mod 1* if for every
subinterval `[a, b) ⊆ [0, 1]` the asymptotic density of the set of indices `n` with
`Int.fract (u n) ∈ [a, b)` exists and equals the length `b - a` of the interval. -/

theorem useq_equidistributed : AsymptoticallyEquidistributedMod1 useq := by
  intro a b ha hab hb
  have hb0 : (0 : ℝ) ≤ b := le_trans ha hab
  have ha1 : a ≤ 1 := le_trans hab hb
  have h1 := tendsto_cnt b hb0 hb
  have h2 := tendsto_cnt a ha ha1
  refine (h1.sub h2).congr fun N => ?_
  rw [card_Ico_eq a b hab N, sub_div]

/-- **Existence of an asymptotically equidistributed sequence.** -/
