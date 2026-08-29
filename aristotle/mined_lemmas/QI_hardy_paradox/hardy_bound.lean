/-
# Hardy Paradox
Category: Frontier Qi
Target: QI.hardy_paradox
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede every command, including module doc comments `/-! -/`,
-- so the required header appears above as an ordinary block comment and is repeated as the
-- module docstring immediately after the imports.)

import Mathlib

/-!
# Hardy Paradox
Category: Frontier Qi
Target: QI.hardy_paradox
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open MeasureTheory

namespace QI

/-!
## Part 1: the local-realistic (hidden-variable) side

A local hidden-variable model for a two-party, two-settings-per-party experiment is a
probability space `Ω` (the space of hidden variables / runs) together with four outcome
functions

* `A₁ A₂ : Ω → Bool` — Alice's outcome for her setting `1` resp. `2`,
* `B₁ B₂ : Ω → Bool` — Bob's outcome for his setting `1` resp. `2`.

Locality and realism are encoded structurally: each outcome is a function of the run `ω`
alone, and in particular Alice's outcome does not depend on Bob's setting and vice versa.
Hardy's argument shows that the four Hardy conditions are then contradictory — a
*logical* (inequality-free) obstruction, unlike CHSH.
-/

/-- The pointwise (run-by-run) core of Hardy's argument: any run in which Alice's second
outcome and Bob's second outcome are both `true` must lie in one of the three Hardy
"forbidden" events. -/

theorem hardy_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A₁ A₂ B₁ B₂ : Ω → Bool) :
    μ {ω | A₂ ω = true ∧ B₂ ω = true} ≤
      μ {ω | A₂ ω = true ∧ B₁ ω = false}
      + μ {ω | A₁ ω = false ∧ B₂ ω = true}
      + μ {ω | A₁ ω = true ∧ B₁ ω = true} := by
  calc μ {ω | A₂ ω = true ∧ B₂ ω = true}
      ≤ _ := measure_mono (hardy_subset A₁ A₂ B₁ B₂)
    _ ≤ _ := le_trans (measure_union_le _ _) (by gcongr; exact measure_union_le _ _)

/-- **Hardy's paradox.**  No local hidden-variable model can reproduce Hardy's four
conditions:

* `A₂ = true` always forces `B₁ = true` (the event `A₂ = true ∧ B₁ = false` is null),
* `B₂ = true` always forces `A₁ = true` (the event `A₁ = false ∧ B₂ = true` is null),
* `A₁ = true ∧ B₁ = true` never happens (null event),
* yet a positive fraction of runs has `A₂ = true ∧ B₂ = true`.

Chaining the first three implications on any run of the (positive-probability) fourth
event yields `A₁ = true ∧ B₁ = true`, a contradiction — no inequality is needed. -/
