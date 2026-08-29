import Mathlib

/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Phys

open Complex MeasureTheory Filter Topology

/-- The expectation value `⟪ψ, A ψ⟫` of an operator `A` in the state `ψ`. -/

theorem gaussian_second_moment :
    ∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2) = Real.sqrt Real.pi / 2 := by
  set f : ℝ → ℝ := fun x => -(1 / 2) * (x * Real.exp (-x ^ 2)) with hf
  set f' : ℝ → ℝ := fun x => x ^ 2 * Real.exp (-x ^ 2) - (1 / 2) * Real.exp (-x ^ 2) with hf'
  have hderiv : ∀ x : ℝ, HasDerivAt f (f' x) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => -x ^ 2) (-(2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).neg
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2)) (Real.exp (-x ^ 2) * (-(2 * x))) x :=
      (Real.hasDerivAt_exp _).comp x h1
    have h3 : HasDerivAt (fun x : ℝ => x * Real.exp (-x ^ 2))
        (1 * Real.exp (-x ^ 2) + x * (Real.exp (-x ^ 2) * (-(2 * x)))) x :=
      (hasDerivAt_id x).mul h2
    have h4 := h3.const_mul (-(1 / 2) : ℝ)
    convert h4 using 1
    simp [hf']
    ring
  have hintf' : Integrable f' := by
    simpa [hf'] using
      integrable_sq_mul_gaussian_kernel.sub (integrable_gaussian_kernel.const_mul (1 / 2 : ℝ))
  have hzero : ∫ x : ℝ, f' x = 0 := by
    have := MeasureTheory.integral_of_hasDerivAt_of_tendsto hderiv hintf'
      (by simpa [hf] using gaussian_tendsto_atBot.const_mul (-(1 / 2) : ℝ))
      (by simpa [hf] using gaussian_tendsto_atTop.const_mul (-(1 / 2) : ℝ))
    simpa using this
  have hsplit : ∫ x : ℝ, f' x
      = (∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2)) - (1 / 2) * ∫ x : ℝ, Real.exp (-x ^ 2) := by
    rw [hf', MeasureTheory.integral_sub integrable_sq_mul_gaussian_kernel
      (integrable_gaussian_kernel.const_mul (1 / 2 : ℝ)), MeasureTheory.integral_const_mul]
  rw [hzero, integral_gaussian_kernel] at hsplit
  linarith

