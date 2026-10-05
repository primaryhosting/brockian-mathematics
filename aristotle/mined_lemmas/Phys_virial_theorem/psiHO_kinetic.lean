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

theorem psiHO_kinetic :
    (∫ x : ℝ, psiHO x * (-(1 / 2) * deriv (deriv psiHO) x)) = 1 / 4 := by
  have hs : Real.sqrt Real.pi ≠ 0 := by positivity
  have hfun : (fun x : ℝ => psiHO x * (-(1 / 2) * deriv (deriv psiHO) x))
      = fun x : ℝ => (-(1 / 2) * (Real.sqrt Real.pi)⁻¹) * (x ^ 2 * Real.exp (-x ^ 2))
          + ((1 / 2) * (Real.sqrt Real.pi)⁻¹) * Real.exp (-x ^ 2) := by
    funext x
    rw [psiHO_deriv2]
    have h1 : psiHO x * (-(1 / 2) * ((x ^ 2 - 1) * psiHO x))
        = -(1 / 2) * (x ^ 2 - 1) * psiHO x ^ 2 := by ring
    rw [h1, psiHO_sq]
    ring
  rw [hfun, MeasureTheory.integral_add (integrable_sq_mul_gaussian_kernel.const_mul _)
      (integrable_gaussian_kernel.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_gaussian_kernel, gaussian_second_moment]
  field_simp
  ring

/-- The expected virial `⟨x V'(x)⟩` of the harmonic oscillator ground state is `1/2`. -/
