import Mathlib
/-!
# Hellmann Feynman
Category: Frontier Phys
Target: Phys.hellmann_feynman
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phys

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The map `λ ↦ H λ (ψ λ)` is differentiable, with the expected product rule, where the
operators `H λ` are `ℂ`-linear but the parameter `λ` is real. -/

theorem inner_deriv_add_deriv_inner_eq_zero
    {psi : ℝ → V} {dpsi : V} {t : ℝ} (hpsi : HasDerivAt psi dpsi t)
    (hnorm : ∀ l, inner ℂ (psi l) (psi l) = 1) :
    inner ℂ (psi t) dpsi + inner ℂ dpsi (psi t) = 0 := by
  have h1 : HasDerivAt (fun l => inner ℂ (psi l) (psi l))
      (inner ℂ (psi t) dpsi + inner ℂ dpsi (psi t)) t := hpsi.inner ℂ hpsi
  have h2 : HasDerivAt (fun _ : ℝ => (1 : ℂ)) 0 t := hasDerivAt_const t 1
  have hfun : (fun l => inner ℂ (psi l) (psi l)) = fun _ : ℝ => (1 : ℂ) := funext hnorm
  rw [hfun] at h1
  exact h1.unique h2

/-- **Hellmann–Feynman theorem.**

Let `λ ↦ H λ` be a family of (bounded, `ℂ`-linear) operators on a complex inner product space,
differentiable at `t` with derivative `dH`, and let `λ ↦ ψ λ` be a differentiable family of
normalized eigenvectors, `H λ (ψ λ) = E λ • ψ λ` with real eigenvalues `E λ`.  If `H t` is
self-adjoint, then the eigenvalue function `E` is differentiable at `t` and

`dE/dλ = ⟪ψ, (dH/dλ) ψ⟫`. -/
