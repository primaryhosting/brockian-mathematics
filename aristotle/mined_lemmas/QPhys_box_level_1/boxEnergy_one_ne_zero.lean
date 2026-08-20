/-
# Box Level 1
Category: Quantum Physics
Target: QPhys.box_level_1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a module docstring `/-!`,
-- because Lean 4 requires `import` to be the first command in a file.)

import Mathlib

/-!
# Box Level 1
Category: Quantum Physics
Target: QPhys.box_level_1
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

namespace QPhys

/-- Energy of the `n`-th stationary state of a particle of mass `m` in a one-dimensional
infinite square well ("particle in a box") of width `L`, with reduced Planck constant `hbar`:
`E n = n² π² ħ² / (2 m L²)`. -/

theorem boxEnergy_one_ne_zero {m L hbar : ℝ} (hm : m ≠ 0) (hL : L ≠ 0) (hbar0 : hbar ≠ 0) :
    boxEnergy m L hbar 1 ≠ 0 := by
  unfold boxEnergy
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  push_cast
  positivity

/-- **Box Level 1.** The infinite-well energy ratio `E₁ / E₁ = 1²`. -/
