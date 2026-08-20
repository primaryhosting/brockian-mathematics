/-
# Hellmann Feynman
Category: Frontier Phys
Target: Phys.hellmann_feynman
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Phys

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- **Key intermediate lemma.** If a curve `ψ` in a complex inner product space stays on the
unit sphere and is differentiable at `l` with derivative `ψ'`, then the derivative is
"orthogonal" to `ψ l` in the sense that `⟪ψ l, ψ'⟫ + ⟪ψ', ψ l⟫ = 0`
(i.e. the real part of `⟪ψ l, ψ'⟫` vanishes). -/

theorem inner_deriv_add_inner_deriv_eq_zero
    {ψ : ℝ → V} {ψ' : V} {l : ℝ}
    (hψ : HasDerivAt ψ ψ' l) (hnorm : ∀ t, ‖ψ t‖ = 1) :
    ⟪ψ l, ψ'⟫_ℂ + ⟪ψ', ψ l⟫_ℂ = 0 := by
  have h : HasDerivAt (fun t => ⟪ψ t, ψ t⟫_ℂ) (⟪ψ l, ψ'⟫_ℂ + ⟪ψ', ψ l⟫_ℂ) l :=
    hψ.inner ℂ hψ
  have h0 : (fun t => ⟪ψ t, ψ t⟫_ℂ) = fun _ => (1 : ℂ) := by
    funext t
    rw [inner_self_eq_norm_sq_to_K, hnorm t]
    norm_num
  rw [h0] at h
  simpa using h.unique (hasDerivAt_const l (1 : ℂ))

/-- **Hellmann–Feynman theorem.**

Let `H : ℝ → (V →L[ℂ] V)` be a family of operators on a complex inner product space depending
on a parameter `λ`, and suppose that for every parameter value `t` the unit vector `ψ t` is an
eigenvector of `H t` with (real) eigenvalue `E t`. If `H`, `ψ` and `E` are differentiable at `l`
and `H l` is symmetric (self-adjoint), then

`dE/dλ = ⟪ψ, (dH/dλ) ψ⟫`. -/
