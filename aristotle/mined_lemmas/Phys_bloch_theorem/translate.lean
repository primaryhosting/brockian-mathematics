/-
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bloch Theorem
Category: Frontier Phys
Target: Phys.bloch_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Phys

open Complex

/-- Translation of a wavefunction by `a`: `(translate a ψ) x = ψ (x + a)`. -/

def translate (a : ℝ) (ψ : ℝ → ℂ) : ℝ → ℂ := fun x => ψ (x + a)

/-- An operator `H` on wavefunctions is `a`-periodic when it commutes with translation
by the lattice constant `a`. -/
