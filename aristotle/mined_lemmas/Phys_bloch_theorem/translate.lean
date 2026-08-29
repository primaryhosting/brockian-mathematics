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

/-- The translation operator by `a` acting on wave functions. -/

def translate (a : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := fun x => f (x + a)

/-- The one-dimensional Schrödinger Hamiltonian `H ψ = -ψ'' + V ψ`. -/
