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

private theorem r11_sq : r11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)

/-- Origin of the spindle. -/
private noncomputable def P0 : ℂ := ⟨0, 0⟩
/-- The point at distance `1` from `P0` whose colour we compare. -/
private noncomputable def P1 : ℂ := ⟨1, 0⟩
/-- The common apex of the two rhombi, at distance `√3` from both `P0` and `P1`. -/
private noncomputable def PT : ℂ := ⟨1 / 2, r11 / 2⟩
/-- First side vertex of the rhombus `P0–PT`. -/
private noncomputable def PA : ℂ := ⟨1 / 4 - r3 * r11 / 12, r11 / 4 + r3 / 12⟩
/-- Second side vertex of the rhombus `P0–PT`. -/
private noncomputable def PB : ℂ := ⟨1 / 4 + r3 * r11 / 12, r11 / 4 - r3 / 12⟩
/-- First side vertex of the rhombus `P1–PT`. -/
private noncomputable def PA' : ℂ := ⟨3 / 4 - r3 * r11 / 12, r11 / 4 - r3 / 12⟩
/-- Second side vertex of the rhombus `P1–PT`. -/
private noncomputable def PB' : ℂ := ⟨3 / 4 + r3 * r11 / 12, r11 / 4 + r3 / 12⟩

