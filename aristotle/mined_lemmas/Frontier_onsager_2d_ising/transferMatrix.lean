import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

namespace Frontier

/-! ## The 2D Ising model on a periodic `m × n` lattice (a torus) -/

/-- Real value of an Ising spin: `true ↦ +1`, `false ↦ -1`. -/

noncomputable def transferMatrix (n : ℕ) [NeZero n] (J β : ℝ) :
    Matrix (ZMod n → Bool) (ZMod n → Bool) ℝ :=
  Matrix.of fun s s' => Real.exp (β * J * ∑ y : ZMod n,
    (spin (s y) * spin (s' y) + spin (s y) * spin (s (y + 1))))

/-! ## Onsager's exact expression -/

/-- The integrand of Onsager's exact solution,
`log (cosh²(2βJ) - sinh(2βJ) (cos θ + cos ψ))`. -/
