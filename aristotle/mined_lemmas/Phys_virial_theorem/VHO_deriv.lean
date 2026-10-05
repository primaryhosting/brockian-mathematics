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

theorem VHO_deriv (x : ℝ) : deriv VHO x = x := by
  have h : HasDerivAt VHO x x := by
    have h0 := (hasDerivAt_pow 2 x).div_const 2
    convert h0 using 1
    push_cast
    ring
  exact h.deriv

/-- The expected kinetic energy of the harmonic oscillator ground state is `1/4`. -/
