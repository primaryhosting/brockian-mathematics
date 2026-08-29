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

/-- `f` has period `a`. -/

theorem translate_pow_neg {a : ℝ} {ψ : ℝ → ℂ} {lam : ℂ}
    (h : ∀ x, ψ (x + a) = lam * ψ x) (n : ℕ) (x : ℝ) :
    ψ x = lam ^ n * ψ (x - n * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hx : (x : ℝ) - (n : ℕ) * a = (x - (n + 1 : ℕ) * a) + a := by push_cast; ring
      rw [ih, hx, h]
      ring

/-- A bounded nonzero solution of the translation eigenvalue equation forces the
eigenvalue to be a unit modulus complex number. -/
