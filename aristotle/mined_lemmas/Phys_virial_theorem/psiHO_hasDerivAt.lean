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

theorem psiHO_hasDerivAt (x : ℝ) : HasDerivAt psiHO (-x * psiHO x) x := by
  have h1 : HasDerivAt (fun x : ℝ => -x ^ 2 / 2) (-x) x := by
    have h0 := ((hasDerivAt_pow 2 x).neg).div_const 2
    convert h0 using 1
    push_cast
    ring
  have h2 : HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2 / 2)) (Real.exp (-x ^ 2 / 2) * (-x)) x :=
    (Real.hasDerivAt_exp _).comp x h1
  have h3 := h2.const_mul (Real.pi ^ (-(1 : ℝ) / 4))
  convert h3 using 1
  simp [psiHO]
  ring

