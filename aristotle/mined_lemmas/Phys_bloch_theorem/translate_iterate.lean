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

theorem translate_iterate {a : ℝ} {ψ : ℝ → ℂ} {lam : ℂ}
    (hT : ∀ x : ℝ, ψ (x + a) = lam * ψ x) (n : ℕ) (x : ℝ) :
    ψ (x + n * a) = lam ^ n * ψ x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      have hx : x + ((n + 1 : ℕ) : ℝ) * a = (x + n * a) + a := by push_cast; ring
      rw [hx, hT, ih]
      ring

/-- The translation eigenvalue of a bounded, not identically vanishing eigenstate has modulus
one.  (Physically this is unitarity of the translation operator; here it is derived from
boundedness of `ψ`.) -/
