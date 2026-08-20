/-
# Particle In Box
Category: Quantum Physics
Target: QPhys.particle_in_box
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QPhys

/-- The `n`-th (unnormalized) stationary state of a particle in an infinite square
well of width `L`: `ψ_n(x) = sin(n π x / L)`. -/

private lemma deriv_const_mul_cos (c : ℝ) :
    deriv (fun x : ℝ => c * Real.cos (c * x)) = fun x : ℝ => -(c ^ 2 * Real.sin (c * x)) := by
  funext x
  have h : HasDerivAt (fun x : ℝ => c * Real.cos (c * x)) (c * (-Real.sin (c * x) * (c * 1))) x :=
    HasDerivAt.const_mul c ((Real.hasDerivAt_cos (c * x)).comp x ((hasDerivAt_id x).const_mul c))
  have := h.deriv
  rw [this]
  ring

/--
**Particle in a one-dimensional infinite square well of width `L`.**

For a particle of mass `m > 0` in a box `[0, L]` (`L > 0`), the wave function
`ψ_n(x) = sin(n π x / L)` (`n ≥ 1`) satisfies:

* the Dirichlet boundary conditions `ψ_n(0) = ψ_n(L) = 0`;
* `ψ_n` is not identically zero;
* the time-independent Schrödinger equation `-(ℏ²/2m) ψ_n'' = E_n ψ_n` with
  `E_n = n² π² ℏ² / (2 m L²)`;

and, conversely, energy is quantized: any wave number `k > 0` compatible with the
boundary condition `sin (k L) = 0` yields an energy `ℏ² k² / (2m)` of the form `E_j`
for some integer `j ≥ 1`.
-/
