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

theorem translate_iterate (a : ℝ) (ψ : ℝ → ℂ) (c : ℂ)
    (hψ : ∀ x, translate a ψ x = c * ψ x) (x : ℝ) :
    ∀ n : ℕ, ψ (x + n * a) = c ^ n * ψ x := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have : ψ (x + n * a + a) = c * ψ (x + n * a) := hψ _
      have hx : x + (n + 1 : ℕ) * a = x + n * a + a := by push_cast; ring
      rw [hx, this, ih]
      ring

/-- A bounded, not identically vanishing eigenfunction of the translation operator has an
eigenvalue of unit modulus.  This is the physical input that turns the eigenvalue into a
phase `e ^ (i k a)`. -/
