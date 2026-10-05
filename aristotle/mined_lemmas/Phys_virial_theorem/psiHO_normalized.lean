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

theorem psiHO_normalized : ∫ x : ℝ, psiHO x ^ 2 = 1 := by
  have hs : Real.sqrt Real.pi ≠ 0 := by positivity
  simp only [psiHO_sq]
  rw [MeasureTheory.integral_const_mul, integral_gaussian_kernel]
  field_simp

