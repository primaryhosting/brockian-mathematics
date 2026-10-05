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

theorem psiHO_deriv_eq : deriv psiHO = fun x => -x * psiHO x :=
  funext fun x => (psiHO_hasDerivAt x).deriv

/-- The ground state satisfies the Schrödinger equation `-½ψ'' + ½x²ψ = ½ψ`, since
`ψ'' = (x² - 1) ψ`. -/
