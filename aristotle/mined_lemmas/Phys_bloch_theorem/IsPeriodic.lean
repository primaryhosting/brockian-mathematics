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

def IsPeriodic (a : ℝ) (f : ℝ → ℂ) : Prop := ∀ x, f (x + a) = f x

/-- `ψ` is an eigenstate of the one-dimensional Hamiltonian `H = -d²/dx² + V`
with energy `E`, i.e. `-ψ'' + V ψ = E ψ`, written as `ψ'' = (V - E) ψ`. -/
