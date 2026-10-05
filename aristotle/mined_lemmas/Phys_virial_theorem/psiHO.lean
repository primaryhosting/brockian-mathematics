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

noncomputable def psiHO (x : ℝ) : ℝ := Real.pi ^ (-(1 : ℝ) / 4) * Real.exp (-x ^ 2 / 2)

/-- The harmonic oscillator potential `V(x) = x²/2`. -/
