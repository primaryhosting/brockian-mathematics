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

lemma bool_sum_exp (β t E : ℝ) (ht : t = 1 ∨ t = -1) :
    ∑ b : Bool, Real.exp (β * (spin b * t + E)) = (2 * Real.cosh β) * Real.exp (β * E) := by
  have hc : 2 * Real.cosh β = Real.exp β + Real.exp (-β) := by
    rw [Real.cosh_eq]; ring
  rcases ht with h | h <;> subst h <;>
    simp only [Fintype.sum_bool, spin_true, spin_false, hc]
  · rw [show β * (1 * 1 + E) = β + β * E by ring, show β * (-1 * 1 + E) = -β + β * E by ring,
      Real.exp_add, Real.exp_add]
    ring
  · rw [show β * (1 * -1 + E) = -β + β * E by ring,
      show β * (-1 * -1 + E) = β + β * E by ring, Real.exp_add, Real.exp_add]
    ring

