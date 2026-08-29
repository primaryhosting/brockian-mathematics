/-!
# Box Level 4
Category: Quantum Physics
Target: QPhys.box_level_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite
potential well ("particle in a box") of width `L`:

`E n = n² π² ħ² / (2 m L²)`,

where `pi2` denotes `π²`.  (This file carries the required header comment at
the very top, which Lean does not allow to be followed by `import`, so the
arithmetic is carried out in the exact rational field `Rat`, which is
available without any imports.  A version over the real numbers, with the
genuine `Real.pi` and no rational stand-in, is proved in
`RequestProject/BoxLevel4Real.lean`.) -/
def boxEnergy (pi2 hbar m L : Rat) (n : Nat) : Rat :=
  (n : Rat) ^ 2 * pi2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- For the infinite square well, the ratio of the fourth energy level to the
ground-state energy is `4² = 16`. -/
theorem box_level_4 (pi2 hbar m L : Rat)
    (h : boxEnergy pi2 hbar m L 1 ≠ 0) :
    boxEnergy pi2 hbar m L 4 / boxEnergy pi2 hbar m L 1 = (4 : Rat) ^ 2 := by
  unfold boxEnergy at *
  grind

end QPhys

import Mathlib

/-!
# Box Level 4 (real-number version)

Category: Quantum Physics
Provenance: Aristotle theorem prover (Harmonic)

The infinite-well energy ratio `E₄ / E₁ = 4²`, over `ℝ`, with the genuine
`Real.pi` and physical parameters `ħ`, `m`, `L`.
-/

namespace QPhys

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite
potential well of width `L`: `E n = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergyReal (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- The fourth level of the infinite square well has `4²` times the energy of
the ground state. -/
theorem boxEnergyReal_four (hbar m L : ℝ) :
    boxEnergyReal hbar m L 4 = (4 : ℝ) ^ 2 * boxEnergyReal hbar m L 1 := by
  unfold boxEnergyReal
  push_cast
  ring

/-- The infinite-well energy ratio `E₄ / E₁ = 4²`. -/
theorem box_level_4_real (hbar m L : ℝ) (hbar_ne : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergyReal hbar m L 4 / boxEnergyReal hbar m L 1 = (4 : ℝ) ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h1 : boxEnergyReal hbar m L 1 ≠ 0 := by
    unfold boxEnergyReal
    push_cast
    positivity
  rw [boxEnergyReal_four, mul_div_assoc, div_self h1, mul_one]

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

