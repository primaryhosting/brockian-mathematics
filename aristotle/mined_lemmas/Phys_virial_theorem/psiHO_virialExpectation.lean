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

theorem psiHO_virialExpectation :
    (∫ x : ℝ, psiHO x * ((x * deriv VHO x) * psiHO x)) = 1 / 2 := by
  have hs : Real.sqrt Real.pi ≠ 0 := by positivity
  have hfun : (fun x : ℝ => psiHO x * ((x * deriv VHO x) * psiHO x))
      = fun x : ℝ => (Real.sqrt Real.pi)⁻¹ * (x ^ 2 * Real.exp (-x ^ 2)) := by
    funext x
    rw [VHO_deriv]
    have h1 : psiHO x * (x * x * psiHO x) = x ^ 2 * psiHO x ^ 2 := by ring
    rw [h1, psiHO_sq]
    ring
  rw [hfun, MeasureTheory.integral_const_mul, gaussian_second_moment]
  field_simp

/-- **The virial theorem for the harmonic oscillator ground state**: with kinetic energy
`T = -½ d²/dx²` and potential `V(x) = x²/2`, the normalized ground state satisfies
`2⟨T⟩ = ⟨x V'(x)⟩` (both sides equal `1/2`). -/
