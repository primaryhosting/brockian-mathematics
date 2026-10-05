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

theorem gaussian_tendsto_atBot : Tendsto (fun x : ℝ => x * Real.exp (-x ^ 2)) atBot (𝓝 0) := by
  have h := (gaussian_tendsto_atTop.comp tendsto_neg_atBot_atTop).neg
  simpa [Function.comp_def] using h

/-- The second moment of the Gaussian: `∫ x² e^{-x²} dx = √π / 2`. -/
