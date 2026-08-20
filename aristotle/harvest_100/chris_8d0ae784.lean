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
theorem hellmann_feynman
    {H : ℝ → (V →L[ℂ] V)} {ψ : ℝ → V} {E : ℝ → ℝ}
    {l : ℝ} {H' : V →L[ℂ] V} {ψ' : V} {E' : ℝ}
    (hH : HasDerivAt H H' l) (hψ : HasDerivAt ψ ψ' l) (hE : HasDerivAt E E' l)
    (hsymm : ∀ x y : V, ⟪H l x, y⟫_ℂ = ⟪x, H l y⟫_ℂ)
    (heig : ∀ t, H t (ψ t) = (E t : ℂ) • ψ t)
    (hnorm : ∀ t, ‖ψ t‖ = 1) :
    (E' : ℂ) = ⟪ψ l, H' (ψ l)⟫_ℂ := by
  -- Restrict scalars so that the product rule for `t ↦ H t (ψ t)` applies over `ℝ`.
  set L : (V →L[ℂ] V) →L[ℝ] (V →L[ℝ] V) :=
    ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ with hL
  have hHr : HasDerivAt (fun t => L (H t)) (L H') l :=
    L.hasFDerivAt.comp_hasDerivAt l hH
  have happ : HasDerivAt (fun t => (L (H t)) (ψ t)) ((L H') (ψ l) + (L (H l)) ψ') l :=
    hHr.clm_apply hψ
  have happ' : HasDerivAt (fun t => H t (ψ t)) (H' (ψ l) + H l ψ') l := happ
  -- Differentiate `t ↦ ⟪ψ t, H t (ψ t)⟫`.
  have hf : HasDerivAt (fun t => ⟪ψ t, (H t) (ψ t)⟫_ℂ)
      (⟪ψ l, H' (ψ l) + H l ψ'⟫_ℂ + ⟪ψ', H l (ψ l)⟫_ℂ) l := hψ.inner ℂ happ'
  -- On the other hand this function is just `E`.
  have hfE : (fun t => ⟪ψ t, (H t) (ψ t)⟫_ℂ) = fun t => ((E t : ℂ)) := by
    funext t
    rw [heig t, inner_smul_right, inner_self_eq_norm_sq_to_K, hnorm t]
    norm_num
  rw [hfE] at hf
  have hEc : HasDerivAt (fun t => ((E t : ℂ))) ((E' : ℂ)) l := hE.ofReal_comp
  have key := hEc.unique hf
  -- Simplify the right-hand side using the eigenvalue equation and symmetry.
  have h1 : ⟪ψ l, H l ψ'⟫_ℂ = (E l : ℂ) * ⟪ψ l, ψ'⟫_ℂ := by
    rw [← hsymm, heig l, inner_smul_left]
    simp
  have h2 : ⟪ψ', H l (ψ l)⟫_ℂ = (E l : ℂ) * ⟪ψ', ψ l⟫_ℂ := by
    rw [heig l, inner_smul_right]
  have h3 : ⟪ψ l, ψ'⟫_ℂ + ⟪ψ', ψ l⟫_ℂ = 0 :=
    inner_deriv_add_inner_deriv_eq_zero hψ hnorm
  rw [inner_add_right, h1, h2] at key
  have : (E l : ℂ) * ⟪ψ l, ψ'⟫_ℂ + (E l : ℂ) * ⟪ψ', ψ l⟫_ℂ = 0 := by
    rw [← mul_add, h3, mul_zero]
  linear_combination key + this

end Phys

