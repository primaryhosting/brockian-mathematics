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

theorem deriv2_boxWave (L : ℝ) (n : ℕ) :
    deriv (deriv (boxWave L n)) = fun x => -(((n : ℝ) * Real.pi / L) ^ 2 * boxWave L n x) := by
  rw [deriv_boxWave]
  set c : ℝ := (n : ℝ) * Real.pi / L with hc
  funext x
  have h : HasDerivAt (fun x : ℝ => c * Real.cos (c * x)) (c * (-Real.sin (c * x) * (c * 1))) x :=
    (HasDerivAt.cos ((hasDerivAt_id x).const_mul c)).const_mul c
  show deriv (fun x : ℝ => c * Real.cos (c * x)) x = _
  rw [boxWave, show -(c ^ 2 * Real.sin (c * x)) = c * (-Real.sin (c * x) * (c * 1)) by ring,
    ← h.deriv]

/-- The stationary state `ψₙ` solves the time-independent Schrödinger equation inside the
well (where the potential vanishes), with eigenvalue `boxEnergy hbar m L n`:
`-(ħ²/2m) ψₙ'' = Eₙ ψₙ`. -/
