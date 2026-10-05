import Mathlib

/-!
# Box Level 2
Category: Quantum Physics
Target: QPhys.box_level_2
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

/-- The `n`-th stationary state of a particle of mass `m` in a one-dimensional
infinite square well ("particle in a box") of width `L`, up to normalization:
`ψ_n(x) = sin (n π x / L)`.  It vanishes at both walls `x = 0` and `x = L`. -/

private theorem deriv_deriv_sin_mul (c x : ℝ) :
    deriv (deriv (fun y : ℝ => Real.sin (c * y))) x = -(Real.sin (c * x) * c ^ 2) := by
  have h : deriv (fun y : ℝ => Real.sin (c * y)) = fun y => Real.cos (c * y) * c := by
    funext y
    exact (by
      simpa using (Real.hasDerivAt_sin (c * y)).comp y ((hasDerivAt_id y).const_mul c) :
      HasDerivAt (fun z : ℝ => Real.sin (c * z)) (Real.cos (c * y) * c) y).deriv
  rw [h]
  have h2 : HasDerivAt (fun y : ℝ => Real.cos (c * y) * c) (-(Real.sin (c * x) * c ^ 2)) x := by
    have := ((Real.hasDerivAt_cos (c * x)).comp x ((hasDerivAt_id x).const_mul c)).mul_const c
    simpa using this.congr_deriv (by ring)
  exact h2.deriv

/-- `boxState L n` is an eigenfunction of the free Hamiltonian `-ħ²/(2m) d²/dx²`
inside the well, with eigenvalue `boxEnergy hbar m L n`.  This justifies the
formula used for the energy levels. -/
