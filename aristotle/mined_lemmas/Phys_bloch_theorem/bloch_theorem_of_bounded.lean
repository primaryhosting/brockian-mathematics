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

theorem bloch_theorem_of_bounded (a : ℝ) (ha : 0 < a) (ψ : ℝ → ℂ) (c : ℂ) (M : ℝ)
    (hbdd : ∀ x, ‖ψ x‖ ≤ M) (x₀ : ℝ) (hx₀ : ψ x₀ ≠ 0)
    (hψ : ∀ x, translate a ψ x = c * ψ x) :
    ∃ k : ℝ, ∃ u : ℝ → ℂ, (∀ x, u (x + a) = u x) ∧
      ∀ x, ψ x = Complex.exp (Complex.I * k * x) * u x :=
  bloch_theorem a ha ψ c (translate_eigenvalue_norm_eq_one a ψ c M hbdd x₀ hx₀ hψ) hψ

/-- A Bloch wave is automatically an eigenfunction of the lattice translation, with
eigenvalue the phase `e ^ (i k a)`; together with `Phys.bloch_theorem` this characterizes
Bloch waves among wave functions. -/
