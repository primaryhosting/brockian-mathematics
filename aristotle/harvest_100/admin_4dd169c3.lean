/-
# Hellmann Feynman
Category: Frontier Phys
Target: Phys.hellmann_feynman
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is a plain block comment and is repeated as a module doc below.)

import Mathlib

/-!
# Hellmann Feynman
Category: Frontier Phys
Target: Phys.hellmann_feynman
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace Phys

/-- **Hellmann–Feynman theorem.**

Let `H : ℝ → (E →L[ℂ] E)` be a family of (bounded) operators on a complex inner product space,
depending on a parameter `l` (the physicists' `λ`), and let `psi : ℝ → E` be a family of
normalized states satisfying the eigenvalue equation `H t (psi t) = (en t) • psi t` with real
eigenvalues `en t`.  If `H` is differentiable at `l` with derivative `H'` (i.e. `∂H/∂λ`) and
`psi` is differentiable at `l`, and `H l` is symmetric (self-adjoint), then the eigenvalue
function `en` is differentiable at `l` with

`dE_n/dλ = ⟪ψ_n, (∂H/∂λ) ψ_n⟫`.

The right-hand side is real (it is the real part of the inner product; the imaginary part
vanishes for a symmetric derivative, but no such hypothesis is needed here since the derivative
of the real function `en` is automatically the real part).

The proof is the standard one: differentiating `en t = ⟪ψ t, H t (ψ t)⟫` gives three terms;
the two terms involving `dψ/dλ` combine, via the eigenvalue equation and symmetry of `H l`,
into `E · d/dλ ⟪ψ, ψ⟫ = 0` because `‖ψ‖ = 1` is constant. -/
theorem hellmann_feynman {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (H : ℝ → (E →L[ℂ] E)) (psi : ℝ → E) (en : ℝ → ℝ) (l : ℝ)
    (H' : E →L[ℂ] E) (psi' : E)
    (hH : HasDerivAt H H' l) (hpsi : HasDerivAt psi psi' l)
    (hnorm : ∀ t, ‖psi t‖ = 1)
    (hsymm : ∀ x y : E, ⟪H l x, y⟫_ℂ = ⟪x, H l y⟫_ℂ)
    (heig : ∀ t, H t (psi t) = (en t : ℂ) • psi t) :
    HasDerivAt en (⟪psi l, H' (psi l)⟫_ℂ).re l := by
  -- normalization in terms of the inner product
  have hself : ∀ t, ⟪psi t, psi t⟫_ℂ = 1 := by
    intro t
    rw [inner_self_eq_norm_sq_to_K, hnorm t]
    norm_num
  -- the eigenvalue is the expectation value of the Hamiltonian
  have hEre : ∀ t, en t = (⟪psi t, H t (psi t)⟫_ℂ).re := by
    intro t
    rw [heig t, inner_smul_right, hself t]
    simp
  -- differentiability of `t ↦ H t (psi t)`
  have hK : HasDerivAt (fun t => (H t).restrictScalars ℝ) (H'.restrictScalars ℝ) l :=
    (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).hasFDerivAt.comp_hasDerivAt l hH
  have happ : HasDerivAt (fun t => H t (psi t)) (H' (psi l) + H l psi') l := by
    simpa using hK.clm_apply hpsi
  have hd : HasDerivAt (fun t => ⟪psi t, H t (psi t)⟫_ℂ)
      (⟪psi l, H' (psi l) + H l psi'⟫_ℂ + ⟪psi', H l (psi l)⟫_ℂ) l :=
    hpsi.inner ℂ happ
  -- `⟪ψ, ψ⟫` is constant, hence its derivative vanishes
  have hconst : HasDerivAt (fun t => ⟪psi t, psi t⟫_ℂ) 0 l := by
    have h : (fun t => ⟪psi t, psi t⟫_ℂ) = fun _ => (1 : ℂ) := funext hself
    rw [h]
    exact hasDerivAt_const _ _
  have hzero : ⟪psi l, psi'⟫_ℂ + ⟪psi', psi l⟫_ℂ = 0 :=
    (hpsi.inner ℂ hpsi).unique hconst
  -- the terms involving `dψ/dλ` cancel
  have key : ⟪psi l, H' (psi l) + H l psi'⟫_ℂ + ⟪psi', H l (psi l)⟫_ℂ
      = ⟪psi l, H' (psi l)⟫_ℂ := by
    have h1 : ⟪psi l, H l psi'⟫_ℂ = (en l : ℂ) * ⟪psi l, psi'⟫_ℂ := by
      rw [← hsymm, heig l, inner_smul_left]
      simp
    have h2 : ⟪psi', H l (psi l)⟫_ℂ = (en l : ℂ) * ⟪psi', psi l⟫_ℂ := by
      rw [heig l, inner_smul_right]
    have h3 : (en l : ℂ) * ⟪psi l, psi'⟫_ℂ + (en l : ℂ) * ⟪psi', psi l⟫_ℂ = 0 := by
      rw [← mul_add, hzero, mul_zero]
    rw [inner_add_right, h1, h2]
    linear_combination h3
  rw [key] at hd
  have hfun : en = fun t => (⟪psi t, H t (psi t)⟫_ℂ).re := funext hEre
  rw [hfun]
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt l hd

end Phys

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

