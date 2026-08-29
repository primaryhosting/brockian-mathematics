import Mathlib
/-!
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
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

/-!
## The Ising model on a finite chain

We set up the nearest-neighbour Ising model with free boundary conditions on the
segment `{0, 1, …, n}` and compute its two-point function exactly.  This is the
one-dimensional base case of the sharpness of the phase transition
(Duminil-Copin–Tassion): the two-point function decays exponentially at *every*
finite inverse temperature, so the critical inverse temperature is `+∞` and the
subcritical phase (exponential decay of correlations, finite susceptibility)
occupies the whole of `[0, ∞)`.
-/

namespace IsingChain

/-- The spin value attached to a Boolean: `true ↦ +1`, `false ↦ -1`. -/

lemma Z_eq (β : ℝ) (n : ℕ) : Z β n = 2 * (2 * Real.cosh β) ^ n := by
  induction n with
  | zero => simpa using Z_zero β
  | succ n ih => rw [Z_succ, ih]; ring

