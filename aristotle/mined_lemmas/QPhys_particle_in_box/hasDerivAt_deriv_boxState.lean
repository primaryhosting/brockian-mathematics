import Mathlib

/-!
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
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

/-- The `n`-th stationary state of a particle in an infinite square well of width `L`,
`ψ_n(x) = √(2/L) · sin(nπx/L)`. -/

theorem hasDerivAt_deriv_boxState (L : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (deriv (boxState L n))
      (-((n * Real.pi / L) ^ 2) * boxState L n x) x := by
  have hd : deriv (boxState L n)
      = fun y : ℝ => Real.sqrt (2 / L) * ((n * Real.pi / L) * Real.cos (n * Real.pi * y / L)) := by
    funext y
    exact (hasDerivAt_boxState L n y).deriv
  have hlin : HasDerivAt (fun y : ℝ => (n : ℝ) * Real.pi * y / L) ((n : ℝ) * Real.pi / L) x := by
    simpa [mul_comm, mul_div_assoc] using
      (((hasDerivAt_id x).const_mul ((n : ℝ) * Real.pi)).div_const L)
  have hcos := (Real.hasDerivAt_cos ((n : ℝ) * Real.pi * x / L)).comp x hlin
  have := ((hcos.const_mul ((n : ℝ) * Real.pi / L)).const_mul (Real.sqrt (2 / L)))
  rw [hd]
  convert this using 1
  simp [boxState]
  ring

/-- The box eigenstates are normalized on the well `[0, L]`. -/
