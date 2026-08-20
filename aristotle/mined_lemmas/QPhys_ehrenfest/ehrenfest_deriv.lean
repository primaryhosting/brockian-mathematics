/-
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The commutator `[H, A] = H A - A H` of two continuous linear operators. -/

theorem ehrenfest_deriv
    (hbar : ℝ) (H : E →L[ℂ] E) (hH : ∀ x y : E, ⟪H x, y⟫_ℂ = ⟪x, H y⟫_ℂ)
    (psi : ℝ → E) (A : ℝ → (E →L[ℂ] E)) (A' : E →L[ℂ] E) (t : ℝ)
    (hpsi : HasDerivAt psi ((-Complex.I / hbar) • H (psi t)) t)
    (hA : HasDerivAt A A' t) :
    deriv (fun s => ⟪psi s, A s (psi s)⟫_ℂ) t
      = (Complex.I / hbar) * ⟪psi t, (commutator H (A t)) (psi t)⟫_ℂ
        + ⟪psi t, A' (psi t)⟫_ℂ :=
  (ehrenfest hbar H hH psi A A' t hpsi hA).deriv

/-- A stationary state: `ψ(t) = e^{-i E₀ t / ℏ} v` for an eigenvector `v` of `H`
with real eigenvalue `E₀`. -/
