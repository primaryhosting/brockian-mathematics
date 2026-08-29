/-
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QPhys

open ContinuousLinearMap

/-- **Ehrenfest theorem.**

Let `psi : ℝ → E` be a state trajectory in a complex inner product space `E`, obeying the
Schrödinger equation `i ℏ ψ'(t) = H ψ(t)` with a (bounded) self-adjoint Hamiltonian `H`, and let
`A : ℝ → (E →L[ℂ] E)` be a (possibly time dependent) observable with time derivative `A'` at `t`.
Writing the expectation value as `⟨A⟩(s) = ⟪ψ(s), A(s) ψ(s)⟫`, we have

`d⟨A⟩/dt = (i/ℏ) ⟪ψ, [H, A] ψ⟫ + ⟪ψ, (∂A/∂t) ψ⟫`,

where `[H, A] = H A - A H`. -/

theorem ehrenfest_deriv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (hbar : ℝ) (hbar_ne : hbar ≠ 0)
    (psi : ℝ → E) (A : ℝ → (E →L[ℂ] E)) (H : E →L[ℂ] E)
    (hH : ∀ x y : E, ⟪H x, y⟫_ℂ = ⟪x, H y⟫_ℂ)
    (t : ℝ) (psi' : E) (A' : E →L[ℂ] E)
    (hpsi : HasDerivAt psi psi' t)
    (hA : HasDerivAt A A' t)
    (hSchrodinger : (Complex.I * (hbar : ℂ)) • psi' = H (psi t)) :
    deriv (fun s => ⟪psi s, A s (psi s)⟫_ℂ) t
      = (Complex.I / (hbar : ℂ)) * ⟪psi t, (H.comp (A t) - (A t).comp H) (psi t)⟫_ℂ
        + ⟪psi t, A' (psi t)⟫_ℂ :=
  (ehrenfest hbar hbar_ne psi A H hH t psi' A' hpsi hA hSchrodinger).deriv

end QPhys

