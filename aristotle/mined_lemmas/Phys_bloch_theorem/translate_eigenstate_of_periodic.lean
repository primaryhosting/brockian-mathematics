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

theorem translate_eigenstate_of_periodic {a : ℝ} {H : (ℝ → ℂ) → (ℝ → ℂ)}
    (hH : PeriodicOperator a H) {ψ : ℝ → ℂ} {E : ℂ} (hψ : H ψ = fun x => E * ψ x) :
    H (translate a ψ) = fun x => E * (translate a ψ) x := by
  rw [hH ψ, hψ]
  rfl

/-- Iterating the translation eigenvalue equation: `ψ (x + n a) = lam ^ n * ψ x`. -/
