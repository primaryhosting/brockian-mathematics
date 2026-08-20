import Mathlib

/-!
# Singular Series Gaps 13501360 — `ZMod`/Mathlib formulation

Companion to `RequestProject/SingularSeriesGaps13501360.lean`.  The target file there is stated
with elementary `Int` arithmetic (it must begin with a fixed header comment, which precludes an
`import` line); here the same mathematics is recorded in the idiomatic Mathlib language of
`Finset ℤ` and `ZMod p`.
-/

namespace Brockian

/-- A finite set of integers misses a residue class modulo `p`. -/

theorem SingularSeriesGaps13501360 :
    ∀ h : Int, 1350 ≤ h → h ≤ 1360 → (Admissible [0, h] ↔ h % 2 = 0) := by
  intro h _ _
  refine ⟨fun hadm => ?_, admissible_pair_of_even⟩
  have hcases : h % 2 = 0 ∨ h % 2 = 1 := by omega
  rcases hcases with h0 | h1
  · exact h0
  · exact absurd hadm (not_admissible_pair_of_odd h1)

end Brockian

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

