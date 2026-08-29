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

private theorem r87_sq : r87 ^ 2 = 87 := Real.sq_sqrt (by norm_num)

/-- First apex. -/
private noncomputable def X0 : EuclideanSpace ℝ (Fin 3) := !₂[-(1 / 2), 0, 0]
/-- Second apex, at distance `1` from `X0`. -/
private noncomputable def Y0 : EuclideanSpace ℝ (Fin 3) := !₂[1 / 2, 0, 0]
/-- The common third apex, at distance `2√6/3` from both `X0` and `Y0`. -/
private noncomputable def T0 : EuclideanSpace ℝ (Fin 3) := !₂[0, r87 / 6, 0]

/-- Vertex of the unit triangle of the bipyramid on `X0, T0`. -/
private noncomputable def Q1 : EuclideanSpace ℝ (Fin 3) :=
  !₂[-(1 / 4) + r2 * r87 / 24, r87 / 12 - r2 / 8, 0]
/-- Vertex of the unit triangle of the bipyramid on `X0, T0`. -/
private noncomputable def Q2 : EuclideanSpace ℝ (Fin 3) :=
  !₂[-(1 / 4) - r2 * r87 / 48, r87 / 12 + r2 / 16, 1 / 2]
/-- Vertex of the unit triangle of the bipyramid on `X0, T0`. -/
private noncomputable def Q3 : EuclideanSpace ℝ (Fin 3) :=
  !₂[-(1 / 4) - r2 * r87 / 48, r87 / 12 + r2 / 16, -(1 / 2)]

/-- Vertex of the unit triangle of the bipyramid on `Y0, T0`. -/
private noncomputable def Q1' : EuclideanSpace ℝ (Fin 3) :=
  !₂[1 / 4 - r2 * r87 / 24, r87 / 12 - r2 / 8, 0]
/-- Vertex of the unit triangle of the bipyramid on `Y0, T0`. -/
private noncomputable def Q2' : EuclideanSpace ℝ (Fin 3) :=
  !₂[1 / 4 + r2 * r87 / 48, r87 / 12 + r2 / 16, 1 / 2]
/-- Vertex of the unit triangle of the bipyramid on `Y0, T0`. -/
private noncomputable def Q3' : EuclideanSpace ℝ (Fin 3) :=
  !₂[1 / 4 + r2 * r87 / 48, r87 / 12 + r2 / 16, -(1 / 2)]

/-- Closes each of the nineteen unit-distance verifications in three-space. -/
local macro "space_dist" : tactic =>
  `(tactic| (rw [dist_space]
             apply sqrt_one_of
             ring_nf
             try simp only [r2_sq, r87_sq]
             try ring_nf
             try norm_num))

