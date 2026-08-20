/-
/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
-- (Lean 4 does not permit a module docstring to precede `import`, so the header above is
-- wrapped in an outer block comment.)
import Mathlib

open Finset Filter MeasureTheory
open scoped Classical

namespace Frontier

/-- `ContainsAP A k` says that the set `A ⊆ ℕ` contains an arithmetic progression
`a, a + d, …, a + (k-1) d` of length `k` with positive common difference `d`. -/

theorem furstenberg_multiple_recurrence_two {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {T : α → α} (hT : MeasurePreserving T μ μ) {E : Set α}
    (hE : MeasurableSet E) (hE0 : μ E ≠ 0) :
    ∃ n > 0, μ (E ∩ T^[n] ⁻¹' E) ≠ 0 :=
  hT.conservative.exists_gt_measure_inter_ne_zero hE.nullMeasurableSet hE0 0

end Frontier

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

