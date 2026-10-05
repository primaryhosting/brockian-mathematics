/-
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Phys

open Complex

/-- `f` has period `a`. -/

def SchrodingerEigenstate (V : ℝ → ℂ) (E : ℂ) (ψ : ℝ → ℂ) : Prop :=
  ∀ x, deriv (deriv ψ) x = (V x - E) * ψ x

/-- `ψ` is a Bloch wave for the lattice spacing `a`: `ψ x = e^{i k x} u x` with `u`
`a`-periodic. -/
