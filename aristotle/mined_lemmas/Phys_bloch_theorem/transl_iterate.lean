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

private lemma transl_iterate {a : ℝ} {ψ : ℝ → ℂ} {c : ℂ}
    (hstep : ∀ x, ψ (x + a) = c * ψ x) : ∀ (n : ℕ) (x : ℝ), ψ (x + n * a) = c ^ n * ψ x := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih =>
    intro x
    have h : x + ((n + 1 : ℕ) : ℝ) * a = (x + n * a) + a := by push_cast; ring
    rw [h, hstep, ih]
    ring

/-- A bounded solution of `ψ (x + a) = c * ψ x` that does not vanish identically forces the
translation eigenvalue `c` to be a phase, `‖c‖ = 1`. -/
