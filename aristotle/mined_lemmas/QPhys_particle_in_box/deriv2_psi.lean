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

/-- The `n`-th (unnormalized) stationary state of a particle in an infinite square
well of width `L`: `ψₙ(x) = sin (n π x / L)`. -/

lemma deriv2_psi (L : ℝ) (n : ℕ) (hL : L ≠ 0) (x : ℝ) :
    deriv (deriv (psi L n)) x = -(((n : ℝ) * Real.pi / L) ^ 2) * psi L n x := by
  rw [psi_eq L n hL, deriv2_sin_lin]

/-- **Particle in a box.**  For an infinite square well of width `L > 0` containing a
particle of mass `m > 0`, the functions `ψₙ(x) = sin (n π x / L)` (`n ≥ 1`) are
nonzero solutions of the time-independent Schrödinger equation
`-(ℏ²/2m) ψ'' = E ψ` obeying the Dirichlet boundary conditions `ψ(0) = ψ(L) = 0`,
with energy eigenvalue `Eₙ = n² π² ℏ² / (2 m L²)`.  Conversely (quantization), a
solution `sin (k x)` with `k > 0` vanishes at `x = L` exactly when `k = n π / L`
for some `n ≥ 1`, so the admissible energies `ℏ² k² / (2 m)` are exactly the `Eₙ`. -/
