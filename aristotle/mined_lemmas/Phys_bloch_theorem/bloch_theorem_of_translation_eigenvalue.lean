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

theorem bloch_theorem_of_translation_eigenvalue {a : ℝ} (ha : 0 < a) {c : ℂ} {psi : ℝ → ℂ}
    (hc : ∀ x, psi (x + a) = c * psi x)
    (hne : ∃ x₀, psi x₀ ≠ 0) (hbdd : ∃ C, ∀ x, ‖psi x‖ ≤ C) :
    ∃ (k : ℝ) (u : ℝ → ℂ), (∀ x, u (x + a) = u x) ∧
      ∀ x, psi x = Complex.exp (Complex.I * k * x) * u x := by
  have hcnorm : ‖c‖ = 1 := norm_eq_one_of_bounded hc hne hbdd
  refine ⟨Complex.arg c / a, fun x => Complex.exp (-(Complex.I * (Complex.arg c / a) * x)) * psi x,
    ?_, ?_⟩
  · intro x
    have ha0 : (a : ℂ) ≠ 0 := by
      simpa using ne_of_gt ha
    have hc0 : c ≠ 0 := by
      intro h
      rw [h] at hcnorm
      simp at hcnorm
    have hexp : Complex.exp (Complex.I * ((Complex.arg c : ℂ) / a) * a) = c := by
      have h1 : Complex.I * ((Complex.arg c : ℂ) / a) * a = (Complex.arg c : ℂ) * Complex.I := by
        field_simp
      rw [h1]
      have h2 := Complex.norm_mul_exp_arg_mul_I c
      rw [hcnorm] at h2
      simpa using h2
    have hx : (-(Complex.I * ((Complex.arg c : ℂ) / a) * ((x : ℂ) + a)))
        = (-(Complex.I * ((Complex.arg c : ℂ) / a) * x))
          + (-(Complex.I * ((Complex.arg c : ℂ) / a) * a)) := by
      ring
    have hshift : Complex.exp (-(Complex.I * ((Complex.arg c : ℂ) / a) * ((x : ℂ) + a)))
        = Complex.exp (-(Complex.I * ((Complex.arg c : ℂ) / a) * x)) * c⁻¹ := by
      rw [hx, Complex.exp_add]
      congr 1
      rw [Complex.exp_neg, hexp]
    simp only [hc x, Complex.ofReal_add, hshift]
    field_simp
  · intro x
    rw [← mul_assoc, ← Complex.exp_add]
    simp

/-- **Bloch's theorem.**  Let `V` be a potential periodic with period `a > 0`, and let `ψ`
be a `C²`, bounded, nonzero eigenstate of the corresponding Schrödinger operator
`-ψ'' + V ψ = E ψ`, whose space of bounded `C²` eigenstates at energy `E` is one-dimensional
(spanned by `ψ`).  Then `ψ` is a Bloch wave: there are a crystal momentum `k : ℝ` and an
`a`-periodic function `u` with `ψ x = e^{i k x} * u x`. -/
