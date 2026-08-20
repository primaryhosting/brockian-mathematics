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

def PeriodicOperator (a : ℝ) (H : (ℝ → ℂ) → (ℝ → ℂ)) : Prop :=
  ∀ ψ : ℝ → ℂ, H (translate a ψ) = translate a (H ψ)

/-- If the Hamiltonian is periodic, translating an eigenstate produces an eigenstate with the
same energy.  (This is the reason one may diagonalize `H` and the translation operator
simultaneously, which is the hypothesis `hT` of `bloch_theorem` below.) -/
