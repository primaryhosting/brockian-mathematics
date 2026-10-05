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

theorem hamiltonian_comm_translate (a : ℝ) (V : ℝ → ℂ) (hV : ∀ x, V (x + a) = V x)
    (ψ : ℝ → ℂ) :
    hamiltonian V (translate a ψ) = translate a (hamiltonian V ψ) := by
  have h1 : deriv (translate a ψ) = translate a (deriv ψ) := by
    funext x
    simpa [translate] using deriv_comp_add_const ψ a x
  have h2 : deriv (deriv (translate a ψ)) = translate a (deriv (deriv ψ)) := by
    funext x
    rw [h1]
    simpa [translate] using deriv_comp_add_const (deriv ψ) a x
  funext x
  simp only [hamiltonian, translate, h2, hV x]

/-- Iterating the translation eigenvalue equation: `ψ (x + n * a) = c ^ n * ψ x`. -/
