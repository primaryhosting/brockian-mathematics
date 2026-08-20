import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QPhys

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Differentiability of a (possibly time-dependent) bounded operator, transported along
`restrictScalars ℝ`. -/

lemma hasDerivAt_apply {A : ℝ → (E →L[ℂ] E)} {A' : E →L[ℂ] E} {psi : ℝ → E} {psi' : E} {t : ℝ}
    (hA : HasDerivAt A A' t) (hpsi : HasDerivAt psi psi' t) :
    HasDerivAt (fun s => (A s) (psi s)) (A' (psi t) + (A t) psi') t :=
  (hasDerivAt_restrictScalars hA).clm_apply hpsi

/-- **Ehrenfest's theorem.**

For a state `ψ : ℝ → E` in a complex inner product space evolving according to the
Schrödinger equation `i ℏ ψ'(t) = H ψ(t)` with a bounded self-adjoint Hamiltonian `H`,
and a (possibly time-dependent) bounded observable `A`, the expectation value
`⟨A⟩(t) = ⟪ψ t, A t (ψ t)⟫` satisfies

`d⟨A⟩/dt = (i/ℏ) ⟨[H, A]⟩ + ⟨∂A/∂t⟩`. -/
