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

/-- The argument of the logarithm in Onsager's exact free energy formula for the
two-dimensional square-lattice Ising model with reduced coupling `K = βJ`. -/

lemma sinh_two_isingCritical : Real.sinh (2 * isingCritical) = 1 := by
  have h2 : (0:ℝ) < 1 + Real.sqrt 2 := by
    have : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    linarith
  have hx : Real.exp (2 * isingCritical) = 1 + Real.sqrt 2 := by
    unfold isingCritical
    rw [show 2 * (Real.log (1 + Real.sqrt 2) / 2) = Real.log (1 + Real.sqrt 2) by ring,
      Real.exp_log h2]
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [Real.sinh_eq, hx, Real.exp_neg, hx]
  field_simp
  nlinarith [hsq, Real.sqrt_nonneg 2]

/-- At the critical coupling the Onsager integrand vanishes exactly at the corner
`θ₁ = θ₂ = 0` (mod `2π`) of the Brillouin zone: this is the source of the singularity. -/
