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

/-! ## The 2D square-lattice Ising model on an `L × L` torus -/

/-- The real spin value `±1` attached to a Boolean spin variable. -/

lemma sinh_two_betaC : Real.sinh (2 * betaC) = 1 := by
  have h2 : (0:ℝ) < 1 + Real.sqrt 2 := by positivity
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hx : 2 * betaC = Real.log (1 + Real.sqrt 2) := by
    unfold betaC; ring
  rw [hx, Real.sinh_eq, Real.exp_log h2, Real.exp_neg, Real.exp_log h2]
  have hne : (1 + Real.sqrt 2) ≠ 0 := ne_of_gt h2
  field_simp
  nlinarith [hs]

/-- Onsager's logarithm has nonnegative argument at every temperature `β ≥ 0`; indeed
`cosh²(2β) - sinh(2β)(cos θ₁ + cos θ₂) ≥ (sinh(2β) - 1)² ≥ 0`. -/
