/-
# Box Level 7
Category: Quantum Physics
Target: QPhys.box_level_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Box Level 7
Category: Quantum Physics
Target: QPhys.box_level_7
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

/-- Energy levels of a quantum particle of mass `m` in a one-dimensional infinite
potential well ("particle in a box") of width `L`, with reduced Planck constant `hbar`:
`Eₙ = n² π² ħ² / (2 m L²)`. -/

theorem boxEnergy_ratio (hbar mass L : ℝ) (hhbar : hbar ≠ 0) (hmass : mass ≠ 0) (hL : L ≠ 0)
    (n k : ℕ) (hk : k ≠ 0) :
    boxEnergy hbar mass L n / boxEnergy hbar mass L k = ((n : ℝ) / (k : ℝ)) ^ 2 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  unfold boxEnergy
  field_simp

/-! ### Physical grounding: the levels `boxEnergy` really are the eigenvalues of the
time-independent Schrödinger equation on the well, for the standing waves vanishing
at both walls. -/

/-- The (unnormalised) stationary states of the one-dimensional infinite well of width
`L`: `ψₙ(x) = sin (n π x / L)`. -/
