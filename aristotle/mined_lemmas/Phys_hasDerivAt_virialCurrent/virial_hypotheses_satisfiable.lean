import Mathlib
/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
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

namespace Phys

open MeasureTheory Filter Topology

/-- The auxiliary ("virial current") function
`F x = c * (x * ψ'(x)^2 + ψ(x) * ψ'(x)) - x * (V x - E) * ψ x ^ 2`
attached to a solution of the stationary Schrödinger equation
`-c * ψ'' + V ψ = E ψ` (here `c = ℏ²/2m`). -/

theorem virial_hypotheses_satisfiable :
    ∃ (psi dpsi ddpsi V dV : ℝ → ℝ) (E : ℝ),
      (∀ x, psi x ≠ 0) ∧
      (∀ x, HasDerivAt psi (dpsi x) x) ∧
      (∀ x, HasDerivAt dpsi (ddpsi x) x) ∧
      (∀ x, HasDerivAt V (dV x) x) ∧
      (∀ x, -((1:ℝ) ^ 2 / (2 * 1)) * ddpsi x + V x * psi x = E * psi x) ∧
      Integrable (fun x => dpsi x ^ 2) volume ∧
      Integrable (fun x => x * dV x * psi x ^ 2) volume ∧
      Tendsto (fun x => x * dpsi x ^ 2) atBot (𝓝 0) ∧
      Tendsto (fun x => x * dpsi x ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun x => psi x * dpsi x) atBot (𝓝 0) ∧
      Tendsto (fun x => psi x * dpsi x) atTop (𝓝 0) ∧
      Tendsto (fun x => x * (V x - E) * psi x ^ 2) atBot (𝓝 0) ∧
      Tendsto (fun x => x * (V x - E) * psi x ^ 2) atTop (𝓝 0) := by
  have hinner : ∀ x : ℝ, HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := fun x =>
    ((hasDerivAt_pow 2 x).neg.div_const 2).congr_deriv (by push_cast; ring)
  have hpsi : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => Real.exp (-y ^ 2 / 2)) (-x * Real.exp (-x ^ 2 / 2)) x := fun x =>
    (hinner x).exp.congr_deriv (by ring)
  have hcube : (fun x : ℝ => x * (-x * Real.exp (-x ^ 2 / 2)) ^ 2)
      = fun x : ℝ => x ^ 3 * Real.exp (-x ^ 2) := by
    funext x; rw [mul_pow, gaussian_sq]; ring
  have hlin : (fun x : ℝ => Real.exp (-x ^ 2 / 2) * (-x * Real.exp (-x ^ 2 / 2)))
      = fun x : ℝ => -(x ^ 1 * Real.exp (-x ^ 2)) := by
    funext x
    have h : Real.exp (-x ^ 2 / 2) * (-x * Real.exp (-x ^ 2 / 2))
        = -(x * Real.exp (-x ^ 2 / 2) ^ 2) := by ring
    rw [h, gaussian_sq]; ring
  have hvir : (fun x : ℝ => x * (x ^ 2 / 2 - 1/2) * Real.exp (-x ^ 2 / 2) ^ 2)
      = fun x : ℝ => (1/2 : ℝ) * (x ^ 3 * Real.exp (-x ^ 2))
          - (1/2 : ℝ) * (x ^ 1 * Real.exp (-x ^ 2)) := by
    funext x; rw [gaussian_sq]; ring
  refine ⟨fun x => Real.exp (-x ^ 2 / 2), fun x => -x * Real.exp (-x ^ 2 / 2),
    fun x => (x ^ 2 - 1) * Real.exp (-x ^ 2 / 2), fun x => x ^ 2 / 2, fun x => x, 1/2,
    fun x => Real.exp_ne_zero _, hpsi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    have hn : HasDerivAt (fun y : ℝ => -y) (-1:ℝ) x := by simpa using (hasDerivAt_id x).neg
    exact (hn.mul (hpsi x)).congr_deriv (by ring)
  · intro x
    exact ((hasDerivAt_pow 2 x).div_const 2).congr_deriv (by push_cast; ring)
  · intro x; ring
  · have h : (fun x : ℝ => (-x * Real.exp (-x ^ 2 / 2)) ^ 2)
        = fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2) := by
      funext x; rw [mul_pow, gaussian_sq]; ring
    rw [h]; exact integrable_sq_mul_gaussian
  · have h : (fun x : ℝ => x * x * Real.exp (-x ^ 2 / 2) ^ 2)
        = fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2) := by
      funext x; rw [gaussian_sq]; ring
    rw [h]; exact integrable_sq_mul_gaussian
  · rw [hcube]; exact tendsto_pow_mul_gaussian_atBot 3
  · rw [hcube]; exact tendsto_pow_mul_gaussian_atTop 3
  · rw [hlin]; simpa using (tendsto_pow_mul_gaussian_atBot 1).neg
  · rw [hlin]; simpa using (tendsto_pow_mul_gaussian_atTop 1).neg
  · have h := ((tendsto_pow_mul_gaussian_atBot 3).const_mul (1/2 : ℝ)).sub
      ((tendsto_pow_mul_gaussian_atBot 1).const_mul (1/2 : ℝ))
    rw [mul_zero, sub_zero] at h
    rw [hvir]; exact h
  · have h := ((tendsto_pow_mul_gaussian_atTop 3).const_mul (1/2 : ℝ)).sub
      ((tendsto_pow_mul_gaussian_atTop 1).const_mul (1/2 : ℝ))
    rw [mul_zero, sub_zero] at h
    rw [hvir]; exact h

end Phys

