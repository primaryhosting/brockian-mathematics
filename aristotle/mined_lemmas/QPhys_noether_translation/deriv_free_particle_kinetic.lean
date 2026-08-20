/-
# Noether Translation
Category: Quantum Physics
Target: QPhys.noether_translation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

/-- **Key lemma.** If a Lagrangian `L : ℝ → ℝ → ℝ` (position, velocity) is invariant under
translations of the position variable, then its partial derivative with respect to position
vanishes identically. -/

theorem deriv_free_particle_kinetic (m u : ℝ) :
    deriv (fun w => m * w ^ 2 / 2) u = m * u := by
  have h : HasDerivAt (fun w : ℝ => m * w ^ 2 / 2) (m * (2 * u ^ 1) / 2) u :=
    ((hasDerivAt_pow 2 u).const_mul m).div_const 2
  rw [h.deriv]
  ring

/-- Non-vacuity check: the hypotheses of `noether_translation` are satisfiable.  The free particle
with Lagrangian `L x u = m * u ^ 2 / 2` on the uniform trajectory `q t = q₀ + v₀ * t` with velocity
`v t = v₀` is translation invariant and satisfies the Euler–Lagrange equation, and its conserved
momentum is `m * v₀`. -/
