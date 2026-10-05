/-!
# Box Level 5
Category: Quantum Physics
Target: QPhys.box_level_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-!
This file must literally begin with the header comment above, which Lean parses as a
module docstring; module docstrings have to precede every `import` command, so this
module is written using only Lean's core library (no `Mathlib` import) and works over
the rationals `Rat`.  The companion file `RequestProject/BoxLevel5Real.lean` states and
proves the same result over the real numbers `ℝ`, with `Real.pi` for `π`.
-/

/-- Energy of the `n`-th level of a particle of mass `m` in a one-dimensional infinite
potential well ("particle in a box") of width `L`, with reduced Planck constant `hbar`
and circle constant `pi`:  `E n = n² π² ħ² / (2 m L²)`. -/

theorem box_level_5_real (hbar m L : ℝ) (hhbar : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergyReal hbar m L 5 / boxEnergyReal hbar m L 1 = 5 ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold boxEnergyReal
  field_simp
  ring

end QPhys

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

