/-
# Hadwiger Nelson 5
Category: Frontier — Moonshot
Target: Frontier.hadwiger_nelson_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring, so the header
-- above is a plain block comment; it is repeated as a docstring below.)

import Mathlib

/-!
# Hadwiger Nelson 5
Category: Frontier — Moonshot
Target: Frontier.hadwiger_nelson_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-!
## Unit-distance colourings

A colouring of a metric space `X` by `k` colours is *proper* (for the unit-distance
graph on `X`) when no two points at distance exactly `1` receive the same colour.
The chromatic number of `X` is `≥ k + 1` exactly when no proper `k`-colouring exists.
-/

/-- `c : X → Fin k` is a proper colouring of the unit-distance graph on the metric
space `X`: points at distance `1` get distinct colours. -/

theorem plane_not_three_colourable : ¬ ∃ c : ℂ → Fin 3, ProperUnitColouring c := by
  rintro ⟨c, hc⟩
  have e1 : c PT = c P0 :=
    fin3_forced (c PA) (c PB) (c PT) (c P0) (hc _ _ d_PA_PB)
      (hc _ _ d_PT_PA) (hc _ _ d_PT_PB)
      (hc _ _ d_P0_PA) (hc _ _ d_P0_PB)
  have e2 : c PT = c P1 :=
    fin3_forced (c PA') (c PB') (c PT) (c P1) (hc _ _ d_PA'_PB')
      (hc _ _ d_PT_PA') (hc _ _ d_PT_PB')
      (hc _ _ d_P1_PA') (hc _ _ d_P1_PB')
  exact hc _ _ d_P0_P1 (e1.symm.trans e2)

end Plane

/-!
## Three-space: `χ(ℝ³) ≥ 5`

The same "spindle" idea works one dimension up, with the rhombus replaced by the
triangular bipyramid: two apexes joined to a unit equilateral triangle.  Under a
proper `4`-colouring the triangle uses three colours, so both apexes must take the
fourth one.  The apex separation is `2√6/3`, and two points at distance `1` can both
be joined to a common third point at that distance, which yields a contradiction.
-/

section Space

private noncomputable def r2 : ℝ := Real.sqrt 2
private noncomputable def r87 : ℝ := Real.sqrt 87

