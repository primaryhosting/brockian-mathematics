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

theorem schrodingerEigenstate_shift {a : ℝ} {V : ℝ → ℂ} {E : ℂ} {ψ : ℝ → ℂ}
    (hV : IsPeriodic a V) (hψ : SchrodingerEigenstate V E ψ) :
    SchrodingerEigenstate V E (fun x => ψ (x + a)) := by
  intro x
  have h1 : deriv (fun y => ψ (y + a)) = fun y => deriv ψ (y + a) := by
    funext y
    exact deriv_comp_add_const ψ a y
  rw [h1]
  have h2 : deriv (fun y => deriv ψ (y + a)) x = deriv (deriv ψ) (x + a) :=
    deriv_comp_add_const (deriv ψ) a x
  rw [h2, hψ (x + a), hV x]

/-- Iterating the translation relation `ψ (x + a) = lam * ψ x`. -/
