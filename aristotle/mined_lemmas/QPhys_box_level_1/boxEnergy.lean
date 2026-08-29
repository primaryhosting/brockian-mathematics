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
# Box Level 1
Category: Quantum Physics
Target: QPhys.box_level_1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite
potential well ("particle in a box") of width `L`, with reduced Planck
constant `hbar`:  `E n = n² π² ħ² / (2 m L²)`. -/

noncomputable def boxEnergy (hbar m L : ℝ) (n : ℕ) : ℝ :=
    (n : ℝ) ^ 2 * (Real.pi ^ 2 * hbar ^ 2) / (2 * m * L ^ 2)

/-- The infinite-well energy ratio `E₁ / E₁ = 1²`, for positive values of the
physical parameters `ħ`, `m`, `L` (which guarantee `E₁ ≠ 0`). -/
