/-
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-! ## The 2D Ising model on a finite torus -/

/-- The real value `±1` of a spin encoded as a `Bool`. -/

theorem onsagerFreeEnergy_eq_single (K : ℝ) (hK : |Real.sinh (2 * K)| ≠ 1) :
    onsagerFreeEnergy K = onsagerFreeEnergySingle K := by
  have hcs : Real.cosh (2 * K) ^ 2 = 1 + Real.sinh (2 * K) ^ 2 := by
    rw [Real.cosh_sq]; ring
  have hinner : ∀ θ₁ : ℝ,
      (∫ θ₂ in (0 : ℝ)..(2 * Real.pi),
        Real.log (Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * (Real.cos θ₁ + Real.cos θ₂)))
        = 2 * Real.pi * Real.log ((Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * Real.cos θ₁ +
            Real.sqrt ((Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * Real.cos θ₁) ^ 2
              - Real.sinh (2 * K) ^ 2)) / 2) := by
    intro θ₁
    have hlt : |Real.sinh (2 * K)| < Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * Real.cos θ₁ := by
      have h1 : Real.sinh (2 * K) * Real.cos θ₁ ≤ |Real.sinh (2 * K)| := by
        calc Real.sinh (2 * K) * Real.cos θ₁ ≤ |Real.sinh (2 * K) * Real.cos θ₁| :=
              le_abs_self _
          _ = |Real.sinh (2 * K)| * |Real.cos θ₁| := abs_mul _ _
          _ ≤ |Real.sinh (2 * K)| * 1 := by
              exact mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ₁) (abs_nonneg _)
          _ = |Real.sinh (2 * K)| := mul_one _
      have h2 : (0 : ℝ) < (|Real.sinh (2 * K)| - 1) ^ 2 := by
        have hne : |Real.sinh (2 * K)| - 1 ≠ 0 := sub_ne_zero.mpr hK
        positivity
      nlinarith [sq_abs (Real.sinh (2 * K)), hcs, h1, h2]
    have hkey := integral_log_sub_mul_cos
      (Real.cosh (2 * K) ^ 2 - Real.sinh (2 * K) * Real.cos θ₁) (Real.sinh (2 * K)) hlt
    rw [← hkey]
    refine intervalIntegral.integral_congr (fun θ₂ _ => ?_)
    congr 1
    ring
  rw [onsagerFreeEnergy, onsagerFreeEnergySingle,
    intervalIntegral.integral_congr (fun θ₁ _ => hinner θ₁),
    intervalIntegral.integral_const_mul]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  congr 1
  field_simp
  ring

/-- **Onsager's solution of the 2D Ising model** (formalized statement together with the
verified base case and reduction).

1. At infinite temperature (`K = 0`) the exact finite-volume free energy per site of the
   Ising model on any `m × n` torus agrees with Onsager's formula, both being `log 2`.
2. Away from the critical couplings `sinh (2K) = ±1`, Onsager's double integral reduces
   to the classical single-integral form. -/
