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

theorem space_not_four_colourable :
    ¬ ∃ c : EuclideanSpace ℝ (Fin 3) → Fin 4, ProperUnitColouring c := by
  rintro ⟨c, hc⟩
  have e1 : c T0 = c X0 :=
    fin4_forced (c Q1) (c Q2) (c Q3) (c T0) (c X0)
      (hc _ _ e_Q1_Q2) (hc _ _ e_Q1_Q3) (hc _ _ e_Q2_Q3)
      (hc _ _ e_T0_Q1) (hc _ _ e_T0_Q2) (hc _ _ e_T0_Q3)
      (hc _ _ e_X0_Q1) (hc _ _ e_X0_Q2) (hc _ _ e_X0_Q3)
  have e2 : c T0 = c Y0 :=
    fin4_forced (c Q1') (c Q2') (c Q3') (c T0) (c Y0)
      (hc _ _ e_Q1'_Q2') (hc _ _ e_Q1'_Q3') (hc _ _ e_Q2'_Q3')
      (hc _ _ e_T0_Q1') (hc _ _ e_T0_Q2') (hc _ _ e_T0_Q3')
      (hc _ _ e_Y0_Q1') (hc _ _ e_Y0_Q2') (hc _ _ e_Y0_Q3')
  exact hc _ _ e_X0_Y0 (e1.symm.trans e2)

end Space

/-!
## `χ(ℝ²) ≥ 5`

De Grey (2018) exhibited a finite set of points of the plane (1581 of them) whose
unit-distance graph has no proper `4`-colouring; the verification of that finite
combinatorial fact is a large computer search and is taken here as the hypothesis
`deGrey`.  Given it, the plane itself admits no proper `4`-colouring.
-/

/-- **Hadwiger–Nelson, lower bound 5.**  If some finite family `v : Fin n → ℂ` of
points of the plane has the property that every `4`-colouring of its index set
identifies two points at distance `1`, then no `4`-colouring of the whole plane is
proper for the unit-distance graph, i.e. the chromatic number of the plane is at
least `5`.

The hypothesis `deGrey` is exactly the finite combinatorial core established by
A. de Grey (2018) by computer search. -/
