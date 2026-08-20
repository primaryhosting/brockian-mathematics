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
