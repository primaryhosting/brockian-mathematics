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

noncomputable def hamiltonian (V ψ : ℝ → ℂ) : ℝ → ℂ :=
  fun x => -deriv (deriv ψ) x + V x * ψ x

/-- If the potential is `a`-periodic, the Hamiltonian commutes with translation by `a`:
this is the structural input of Bloch's theorem, which lets one diagonalize `H` and the
translation operator simultaneously. -/
