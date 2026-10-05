/-!
# Box Level 4
Category: Quantum Physics
Target: QPhys.box_level_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the shape of this file: Lean 4 requires every `import` command to come before any
other command, including a module docstring.  Since the header comment above must literally
be the first thing in the file, this file cannot import Mathlib, and is therefore developed
in plain Lean 4 core over the rationals, with the energy scale `c = π²ℏ²/(2mL²)` of the well
kept as a parameter.  The fully explicit real-valued companion statement (with `π`, `ℏ`, the
mass `m` and the width `L` spelled out over `ℝ`) is proved as `QPhys.box_level_4_real` in
`RequestProject/BoxLevel4Real.lean`.
-/

namespace QPhys

/-- Energy levels of a particle in a one-dimensional infinite square well
("particle in a box"):  `Eₙ = n² · c`, where `c = π²ℏ²/(2mL²)` is the energy scale of the
well (so `c = E₁` is the ground-state energy). -/

theorem box_level_4_real (hbar m L : ℝ) (hbar_ne : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergyReal hbar m L 4 / boxEnergyReal hbar m L 1 = (4 : ℝ) ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold boxEnergyReal
  push_cast
  field_simp

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

