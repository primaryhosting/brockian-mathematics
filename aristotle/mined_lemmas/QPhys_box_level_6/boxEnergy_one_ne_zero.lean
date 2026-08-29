import Mathlib
/-!
# Box Level 6
Category: Quantum Physics
Target: QPhys.box_level_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- NOTE: Lean 4 requires `import` lines to precede every command, including
-- module documentation comments such as the header above; the header is
-- therefore placed immediately after the single `import Mathlib` line.

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

/-- Energy levels of a quantum particle of mass `m` in a one-dimensional
infinite potential well ("particle in a box") of width `L`, with reduced
Planck constant `hbar`:
`E n = n² π² ħ² / (2 m L²)`. -/

theorem boxEnergy_one_ne_zero {hbar m L : ℝ} (hbar0 : hbar ≠ 0) (hm : m ≠ 0)
    (hL : L ≠ 0) : boxEnergy hbar m L 1 ≠ 0 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold boxEnergy
  simp only [ne_eq, div_eq_zero_iff, not_or]
  refine ⟨by positivity, by positivity⟩

/-- **Infinite square well, level 6.**
The ratio of the sixth energy level to the ground-state energy of a particle
in a one-dimensional infinite potential well equals `6² = 36`. -/
