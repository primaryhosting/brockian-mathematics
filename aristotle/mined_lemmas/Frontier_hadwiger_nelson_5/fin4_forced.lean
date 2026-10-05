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

private theorem fin4_forced :
    ∀ a b c p q : Fin 4, a ≠ b → a ≠ c → b ≠ c →
      p ≠ a → p ≠ b → p ≠ c → q ≠ a → q ≠ b → q ≠ c → p = q := by decide

/-!
## The plane: `χ(ℝ²) ≥ 4`

We use the Moser spindle, realised in `ℂ` with explicit coordinates.  The two
"rhombus" gadgets `{P₀, A, B, T}` and `{P₁, A', B', T}` each force their two apexes
to share a colour under any proper `3`-colouring; since `P₀` and `P₁` are at distance
`1` this is a contradiction.
-/

section Plane

private noncomputable def r3 : ℝ := Real.sqrt 3
private noncomputable def r11 : ℝ := Real.sqrt 11

