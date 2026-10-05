/-
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The expectation value `⟨A⟩ (t) = ⟪ψ t, A t (ψ t)⟫` of a (possibly time-dependent)
observable `A` in the state `ψ t`. -/

theorem ehrenfest_timeIndependent
    (hbar : ℝ) (H : E →L[ℂ] E)
    (hH : ∀ x y : E, inner ℂ (H x) y = inner ℂ x (H y))
    (psi : ℝ → E) (A : E →L[ℂ] E) (t : ℝ)
    (hpsi : HasDerivAt psi ((-Complex.I / (hbar : ℂ)) • H (psi t)) t) :
    deriv (expVal psi (fun _ => A)) t =
      (Complex.I / (hbar : ℂ)) * inner ℂ (psi t) (commutator H A (psi t)) := by
  have h := ehrenfest hbar H hH psi (fun _ => A) (fun _ => 0) t hpsi (hasDerivAt_const t A)
  simpa using h

/-- The hypotheses of `ehrenfest` are non-vacuous: on the one-dimensional Hilbert space `ℂ`,
with Hamiltonian `H = e` (multiplication by a real energy `e`), the state
`ψ t = exp(-i e t/ℏ) ψ₀` solves the Schrödinger equation, and the observable `A t = t`
is a genuinely time-dependent differentiable family with nonzero time derivative. -/
