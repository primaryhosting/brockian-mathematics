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

theorem psiHO_deriv2 (x : ℝ) : deriv (deriv psiHO) x = (x ^ 2 - 1) * psiHO x := by
  rw [psiHO_deriv_eq]
  have h : HasDerivAt (fun y : ℝ => -y * psiHO y) (-1 * psiHO x + -x * (-x * psiHO x)) x :=
    ((hasDerivAt_id x).neg).mul (psiHO_hasDerivAt x)
  rw [h.deriv]
  ring

