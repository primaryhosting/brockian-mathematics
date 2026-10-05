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

Eigenstates of a periodic Hamiltonian are Bloch waves `e^{ikx} u_k(x)`.

The development is organised as follows.

* `Phys.schrodinger` : the one-dimensional Schrödinger operator `ψ ↦ -ψ'' + V ψ`.
* `Phys.IsEigenstate` : `ψ` solves `-ψ'' + V ψ = E ψ`.
* `Phys.isEigenstate_translate` : the Hamiltonian commutes with translation by a period of `V`.
* `Phys.norm_eq_one_of_bounded` : a bounded nonzero `ψ` with `ψ (x + a) = c ψ (x)` has `‖c‖ = 1`.
* `Phys.bloch_theorem` : the main result.
* `Phys.bloch_theorem_of_translation_eigenvalue` : the same conclusion starting directly from
  the translation-eigenvalue property.
* `Phys.bloch_hypotheses_satisfiable` : the hypotheses of `bloch_theorem` are consistent
  (they are met by the constant potential with the constant eigenstate).
-/

namespace Phys

open Complex

/-- The one-dimensional Schrödinger operator with potential `V` (units `ℏ²/2m = 1`),
acting on functions `ψ : ℝ → ℂ`. -/

theorem isEigenstate_translate {a : ℝ} {V : ℝ → ℂ} (hV : ∀ x, V (x + a) = V x)
    {E : ℂ} {psi : ℝ → ℂ} (h : IsEigenstate V E psi) :
    IsEigenstate V E (fun y => psi (y + a)) := by
  have h1 : deriv (fun y => psi (y + a)) = fun y => deriv psi (y + a) := by
    funext y
    exact deriv_comp_add_const psi a y
  have h2 : deriv (deriv (fun y => psi (y + a))) = fun y => deriv (deriv psi) (y + a) := by
    rw [h1]
    funext y
    exact deriv_comp_add_const (deriv psi) a y
  intro x
  have hx := h (x + a)
  simp only [schrodinger, h2, hV x] at *
  linear_combination hx

/-- If `ψ (x + a) = c * ψ x` for all `x`, then `ψ (x + n * a) = c ^ n * ψ x`. -/
