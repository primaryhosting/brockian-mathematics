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

theorem translate_eigen_of_bloch (a k : ℝ) (ψ u : ℝ → ℂ) (hu : ∀ x, u (x + a) = u x)
    (hψ : ∀ x, ψ x = Complex.exp (Complex.I * k * x) * u x) :
    ∀ x, translate a ψ x = Complex.exp (Complex.I * k * a) * ψ x := by
  intro x
  simp only [translate, hψ, hu x]
  push_cast
  rw [← mul_assoc, ← Complex.exp_add]
  ring_nf

/-- **Bloch's theorem for a periodic Hamiltonian.**  Let `V` be `a`-periodic and let `ψ` be a
bounded, nonzero eigenfunction of `H = -d²/dx² + V` with eigenvalue `E`, whose eigenspace is
one-dimensional (spanned by `ψ`).  Then `ψ` is a Bloch wave `e ^ (i k x) * u x` with `u`
`a`-periodic. -/
