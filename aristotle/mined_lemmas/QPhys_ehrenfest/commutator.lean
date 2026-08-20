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

def commutator (H A : E →L[ℂ] E) : E →L[ℂ] E := H.comp A - A.comp H

/--
**Ehrenfest's theorem.**

Let `psi : ℝ → E` be a state trajectory in a complex inner product space obeying the
Schrödinger equation `iℏ ψ'(t) = H ψ(t)` (written here as `ψ'(t) = (-i/ℏ) • H (ψ t)`),
with `H` a symmetric (bounded) Hamiltonian, and let `A : ℝ → (E →L[ℂ] E)` be a
(possibly time-dependent) observable with derivative `A'` at `t`.

Then the expectation value `⟨A⟩(t) = ⟪ψ t, A t (ψ t)⟫` is differentiable at `t` with

`d⟨A⟩/dt = (i/ℏ) ⟪ψ, [H, A] ψ⟫ + ⟪ψ, (∂A/∂t) ψ⟫`.
-/
