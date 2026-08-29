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


namespace Phys

open Complex

/-- The translation operator `(T_a φ)(x) = φ (x + a)`, as a `ℂ`-linear map on wavefunctions. -/

@[simp] lemma transl_apply (a : ℝ) (φ : ℝ → ℂ) (x : ℝ) : transl a φ x = φ (x + a) := rfl

/-- Iterating the translation eigenvalue relation `ψ (x + a) = c * ψ x`. -/
