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

lemma onsagerArg_nonneg {β : ℝ} (hβ : 0 ≤ β) (θ₁ θ₂ : ℝ) : 0 ≤ onsagerArg β θ₁ θ₂ := by
  have hs : 0 ≤ Real.sinh (2 * β) := Real.sinh_nonneg_iff.mpr (by linarith)
  have hc : Real.cosh (2 * β) ^ 2 = 1 + Real.sinh (2 * β) ^ 2 := by
    have := Real.cosh_sq (2 * β)
    nlinarith [Real.sinh_sq (2 * β)]
  have h1 : Real.cos θ₁ ≤ 1 := Real.cos_le_one θ₁
  have h2 : Real.cos θ₂ ≤ 1 := Real.cos_le_one θ₂
  have key : Real.sinh (2 * β) * (Real.cos θ₁ + Real.cos θ₂) ≤ Real.sinh (2 * β) * 2 := by
    apply mul_le_mul_of_nonneg_left _ hs
    linarith
  simp only [onsagerArg]
  nlinarith [sq_nonneg (Real.sinh (2 * β) - 1)]

/-- The argument of Onsager's logarithm degenerates (the free energy is singular)
exactly at the critical temperature. -/
