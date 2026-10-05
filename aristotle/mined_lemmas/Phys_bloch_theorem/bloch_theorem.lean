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

theorem bloch_theorem (a : ℝ) (ha : 0 < a) (ψ : ℝ → ℂ) (c : ℂ) (hc : ‖c‖ = 1)
    (hψ : ∀ x, translate a ψ x = c * ψ x) :
    ∃ k : ℝ, ∃ u : ℝ → ℂ, (∀ x, u (x + a) = u x) ∧
      ∀ x, ψ x = Complex.exp (Complex.I * k * x) * u x := by
  have hcexp : Complex.exp (Complex.arg c * Complex.I) = c := by
    have := Complex.norm_mul_exp_arg_mul_I c
    rw [hc] at this
    simpa using this
  refine ⟨Complex.arg c / a, fun x => Complex.exp (-(Complex.I * (Complex.arg c / a) * x)) * ψ x,
    ?_, ?_⟩
  · intro x
    have hx : ψ (x + a) = c * ψ x := hψ x
    have hane : (a : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt ha
    have hsplit : -(Complex.I * ((Complex.arg c : ℂ) / a) * ((x : ℂ) + a))
        = -(Complex.I * ((Complex.arg c : ℂ) / a) * x) + -((Complex.arg c : ℂ) * Complex.I) := by
      field_simp
      ring
    rw [show ((x : ℝ) + a : ℝ) = (x + a : ℝ) from rfl]
    push_cast
    rw [hx, hsplit, Complex.exp_add]
    rw [show Complex.exp (-((Complex.arg c : ℂ) * Complex.I))
        = (Complex.exp ((Complex.arg c : ℂ) * Complex.I))⁻¹ by
      rw [← Complex.exp_neg]]
    rw [hcexp]
    have hc0 : c ≠ 0 := by
      intro h
      rw [h] at hc
      simp at hc
    field_simp
  · intro x
    rw [← mul_assoc, ← Complex.exp_add]
    simp

/-- Bloch's theorem for a bounded, nonzero eigenfunction of the lattice translation: no
assumption on the eigenvalue `c` is needed, its unit modulus is forced by boundedness. -/
