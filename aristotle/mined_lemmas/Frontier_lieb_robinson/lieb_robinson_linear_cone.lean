import Mathlib

/-!
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open NormedSpace

/-- In a complex Banach algebra, `exp (x + y) = exp x * exp y` for commuting `x`, `y`. -/

theorem lieb_robinson_linear_cone {𝒜 : Type*} [NormedRing 𝒜] [StarRing 𝒜] [CStarRing 𝒜]
    [NormedAlgebra ℂ 𝒜] [StarModule ℂ 𝒜] [CompleteSpace 𝒜] [Nontrivial 𝒜]
    (H A B : 𝒜) (hH : IsSelfAdjoint H) (t : ℝ) (hAB : A * B = B * A) :
    ‖heisenberg H t A * B - B * heisenberg H t A‖ ≤
      4 * ‖A‖ * ‖B‖ * (‖H‖ * |t|) * Real.exp (‖H‖ * |t|) := by
  set r := ‖H‖ * |t|
  have hr0 : 0 ≤ r := mul_nonneg (norm_nonneg H) (abs_nonneg t)
  -- `e^r - 1 ≤ r e^r`
  have hexp : Real.exp r - 1 ≤ r * Real.exp r := by
    have h := Real.add_one_le_exp (-r)
    have hpos : (0 : ℝ) < Real.exp r := Real.exp_pos r
    have := mul_le_mul_of_nonneg_right h (le_of_lt hpos)
    rw [← Real.exp_add] at this
    simp only [neg_add_cancel, Real.exp_zero] at this
    nlinarith
  calc ‖heisenberg H t A * B - B * heisenberg H t A‖
      ≤ 2 * ‖A‖ * ‖B‖ * min 1 (2 * (Real.exp r - 1)) := lieb_robinson H A B hH t hAB
    _ ≤ 2 * ‖A‖ * ‖B‖ * (2 * (Real.exp r - 1)) := by
        have : min 1 (2 * (Real.exp r - 1)) ≤ 2 * (Real.exp r - 1) := min_le_right _ _
        exact mul_le_mul_of_nonneg_left this
          (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg A)) (norm_nonneg B))
    _ ≤ 2 * ‖A‖ * ‖B‖ * (2 * (r * Real.exp r)) := by
        have : 2 * (Real.exp r - 1) ≤ 2 * (r * Real.exp r) := by linarith
        exact mul_le_mul_of_nonneg_left this
          (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg A)) (norm_nonneg B))
    _ = 4 * ‖A‖ * ‖B‖ * r * Real.exp r := by ring

omit [StarRing 𝒜] [CStarRing 𝒜] [StarModule ℂ 𝒜] [CompleteSpace 𝒜] [Nontrivial 𝒜] in
/-- **Strict locality (zero Lieb–Robinson velocity).** If the Hamiltonian commutes with `B`
(the dynamics does not couple the region of `B` to anything else) and `A` commutes with `B`,
then the commutator stays exactly zero at all times: the light cone has zero width. -/
