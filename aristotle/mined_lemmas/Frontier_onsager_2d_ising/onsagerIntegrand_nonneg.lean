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

lemma onsagerIntegrand_nonneg (K t₁ t₂ : ℝ) : 0 ≤ onsagerIntegrand K t₁ t₂ := by
  have hc : Real.cosh (2 * K) ^ 2 = 1 + Real.sinh (2 * K) ^ 2 := by
    have := Real.cosh_sq (2 * K)
    linarith [Real.sinh_sq (2 * K)]
  have h1 : Real.cos t₁ ≤ 1 := Real.cos_le_one t₁
  have h2 : Real.cos t₂ ≤ 1 := Real.cos_le_one t₂
  have h1' : -1 ≤ Real.cos t₁ := Real.neg_one_le_cos t₁
  have h2' : -1 ≤ Real.cos t₂ := Real.neg_one_le_cos t₂
  set s := Real.sinh (2 * K) with hs
  have key : 0 ≤ (|s| - 1) ^ 2 := sq_nonneg _
  have habs : s * (Real.cos t₁ + Real.cos t₂) ≤ 2 * |s| := by
    have : s * (Real.cos t₁ + Real.cos t₂) ≤ |s * (Real.cos t₁ + Real.cos t₂)| := le_abs_self _
    have h3 : |s * (Real.cos t₁ + Real.cos t₂)| = |s| * |Real.cos t₁ + Real.cos t₂| := abs_mul _ _
    have h4 : |Real.cos t₁ + Real.cos t₂| ≤ 2 := by
      rw [abs_le]; constructor <;> [linarith [Real.neg_one_le_cos t₁, Real.neg_one_le_cos t₂];
        linarith]
    nlinarith [abs_nonneg s]
  have hsq : |s| ^ 2 = s ^ 2 := sq_abs s
  unfold onsagerIntegrand
  nlinarith [key, habs, hsq, hc]

