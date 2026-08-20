/-
# Hellmann Feynman
Category: Frontier Phys
Target: Phys.hellmann_feynman
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 1000000

namespace Phys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

omit [IsScalarTower ℝ ℂ E] in
/-- **Key intermediate lemma.** If a curve `ψ : ℝ → E` in a complex inner product space stays on
the unit sphere and is differentiable at `l` with derivative `ψ'`, then
`⟪ψ l, ψ'⟫ + ⟪ψ', ψ l⟫ = 0`, i.e. the velocity is "orthogonal" to the state
(twice the real part of `⟪ψ l, ψ'⟫` vanishes). -/
theorem inner_deriv_add_inner_deriv_eq_zero_of_norm_one
    (psi : ℝ → E) (psi' : E) (l : ℝ)
    (hpsi : HasDerivAt psi psi' l) (hnorm : ∀ t, ‖psi t‖ = 1) :
    (inner ℂ (psi l) psi' : ℂ) + (inner ℂ psi' (psi l) : ℂ) = 0 := by
  have hderiv : HasDerivAt (fun t => (inner ℂ (psi t) (psi t) : ℂ))
      ((inner ℂ (psi l) psi' : ℂ) + (inner ℂ psi' (psi l) : ℂ)) l := hpsi.inner ℂ hpsi
  have hconst : (fun t => (inner ℂ (psi t) (psi t) : ℂ)) = fun _ => (1 : ℂ) := by
    funext t
    rw [inner_self_eq_norm_sq_to_K, hnorm t]
    norm_num
  rw [hconst] at hderiv
  exact hderiv.unique (hasDerivAt_const l (1 : ℂ))

/-- **Hellmann–Feynman theorem.**

Let `H : ℝ → (E →L[ℂ] E)` be a family of self-adjoint operators on a complex inner product space,
depending on a real parameter `l`, and suppose that for every parameter value `t` the vector
`psi t` is a normalized eigenvector of `H t` with (real) eigenvalue `Ev t`.  If the family `H`,
the eigenvector `psi` and the eigenvalue `Ev` are differentiable at `l`, with derivatives
`H'`, `psi'` and `Ev'`, then

`dE/dl = ⟪ψ, (dH/dl) ψ⟫`. -/
theorem hellmann_feynman
    (H : ℝ → (E →L[ℂ] E)) (psi : ℝ → E) (Ev : ℝ → ℝ)
    (l : ℝ) (H' : E →L[ℂ] E) (psi' : E) (Ev' : ℝ)
    (hH : HasDerivAt H H' l)
    (hpsi : HasDerivAt psi psi' l)
    (hEv : HasDerivAt Ev Ev' l)
    (hsa : ∀ x y : E, (inner ℂ (H l x) y : ℂ) = (inner ℂ x (H l y) : ℂ))
    (heig : ∀ t, H t (psi t) = ((Ev t : ℂ)) • psi t)
    (hnorm : ∀ t, ‖psi t‖ = 1) :
    (Ev' : ℂ) = (inner ℂ (psi l) (H' (psi l)) : ℂ) := by
  -- The function `t ↦ ⟪ψ t, H t (ψ t)⟫` is differentiable at `l`.
  have hHr : HasDerivAt (fun t => (H t).restrictScalars ℝ) (H'.restrictScalars ℝ) l :=
    (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).hasFDerivAt.comp_hasDerivAt l hH
  have happ : HasDerivAt (fun t => (H t) (psi t)) (H' (psi l) + (H l) psi') l :=
    hHr.clm_apply hpsi
  have hG : HasDerivAt (fun t => (inner ℂ (psi t) ((H t) (psi t)) : ℂ))
      ((inner ℂ (psi l) (H' (psi l) + (H l) psi') : ℂ)
        + (inner ℂ psi' ((H l) (psi l)) : ℂ)) l := hpsi.inner ℂ happ
  -- But this function is just `t ↦ Ev t`, whose derivative is `Ev'`.
  have hEvC : HasDerivAt (fun t => ((Ev t : ℝ) : ℂ)) ((Ev' : ℝ) : ℂ) l := hEv.ofReal_comp
  have hGeq : (fun t => (inner ℂ (psi t) ((H t) (psi t)) : ℂ)) = fun t => ((Ev t : ℝ) : ℂ) := by
    funext t
    rw [heig t, inner_smul_right, inner_self_eq_norm_sq_to_K, hnorm t]
    norm_num
  rw [hGeq] at hG
  have hEq := hG.unique hEvC
  -- Simplify the derivative using self-adjointness and the normalization condition.
  have h1 : (inner ℂ (psi l) ((H l) psi') : ℂ)
      = (Ev l : ℂ) * (inner ℂ (psi l) psi' : ℂ) := by
    rw [← hsa (psi l) psi', heig l, inner_smul_left]
    simp
  have h2 : (inner ℂ psi' ((H l) (psi l)) : ℂ)
      = (Ev l : ℂ) * (inner ℂ psi' (psi l) : ℂ) := by
    rw [heig l, inner_smul_right]
  have hkey := inner_deriv_add_inner_deriv_eq_zero_of_norm_one psi psi' l hpsi hnorm
  rw [inner_add_right, h1, h2] at hEq
  have : (Ev l : ℂ) * ((inner ℂ (psi l) psi' : ℂ) + (inner ℂ psi' (psi l) : ℂ)) = 0 := by
    rw [hkey, mul_zero]
  linear_combination -hEq + this

/-- Real-valued form of the Hellmann–Feynman theorem: the derivative of the eigenvalue equals the
real part of the expectation value of `dH/dl` in the state `psi l`. -/
theorem hellmann_feynman_re
    (H : ℝ → (E →L[ℂ] E)) (psi : ℝ → E) (Ev : ℝ → ℝ)
    (l : ℝ) (H' : E →L[ℂ] E) (psi' : E) (Ev' : ℝ)
    (hH : HasDerivAt H H' l)
    (hpsi : HasDerivAt psi psi' l)
    (hEv : HasDerivAt Ev Ev' l)
    (hsa : ∀ x y : E, (inner ℂ (H l x) y : ℂ) = (inner ℂ x (H l y) : ℂ))
    (heig : ∀ t, H t (psi t) = ((Ev t : ℂ)) • psi t)
    (hnorm : ∀ t, ‖psi t‖ = 1) :
    Ev' = (inner ℂ (psi l) (H' (psi l)) : ℂ).re := by
  rw [← hellmann_feynman H psi Ev l H' psi' Ev' hH hpsi hEv hsa heig hnorm]
  simp

end Phys

