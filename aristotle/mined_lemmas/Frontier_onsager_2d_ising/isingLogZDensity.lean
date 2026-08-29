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

noncomputable def isingLogZDensity (m n : ℕ) [NeZero m] [NeZero n] (J β : ℝ) : ℝ :=
  (1 / ((m : ℝ) * n)) * Real.log (isingZ m n J β)

/-- The Onsager–Kramers–Wannier **transfer matrix** of the 2D Ising model: it is indexed by
the states `s : ZMod n → Bool` of a single row of `n` spins, and
`T s s' = exp (β J (∑_y s_y s'_y + ∑_y s_y s_{y+1}))` accounts for all the bonds between
two consecutive rows together with the bonds inside the first of them. -/
