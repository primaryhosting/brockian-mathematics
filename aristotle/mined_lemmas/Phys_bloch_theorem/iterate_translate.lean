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

theorem iterate_translate {a : ℝ} {c : ℂ} {psi : ℝ → ℂ}
    (hc : ∀ x, psi (x + a) = c * psi x) (n : ℕ) (x : ℝ) :
    psi (x + n * a) = c ^ n * psi x := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : (x + (n : ℝ) * a) + a = x + ((n : ℕ) + 1 : ℕ) * a := by push_cast; ring
      calc psi (x + ((n : ℕ) + 1 : ℕ) * a) = psi ((x + (n : ℝ) * a) + a) := by rw [hstep]
        _ = c * psi (x + (n : ℝ) * a) := hc _
        _ = c * (c ^ n * psi x) := by rw [ih]
        _ = c ^ (n + 1) * psi x := by ring

/-- A bounded, nonzero function satisfying `ψ (x + a) = c * ψ x` forces `‖c‖ = 1`:
the translation eigenvalue is a pure phase. -/
