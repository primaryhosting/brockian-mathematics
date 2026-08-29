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

theorem translate_pow {a : ℝ} {ψ : ℝ → ℂ} {lam : ℂ}
    (h : ∀ x, ψ (x + a) = lam * ψ x) (n : ℕ) (x : ℝ) :
    ψ (x + n * a) = lam ^ n * ψ x := by
  induction n with
  | zero => simp
  | succ n ih =>
      have : (x : ℝ) + (n + 1 : ℕ) * a = (x + n * a) + a := by push_cast; ring
      rw [this, h (x + n * a), ih]
      ring

/-- Backward iteration of the translation relation. -/
