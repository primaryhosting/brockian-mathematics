/-
# Hellmann Feynman
Category: Frontier Phys
Target: Phys.hellmann_feynman
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring; the header above is a plain
-- block comment with the exact required text, repeated below as a module docstring.)

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

/-- **Hellmann–Feynman theorem.**

Let `H : ℝ → (F →L[ℂ] F)` be a family of symmetric (Hermitian) operators on a complex inner
product space `F`, depending on a parameter `λ`, and let `ψ : ℝ → F` be a family of normalized
eigenvectors, `H λ (ψ λ) = E λ • ψ λ` with real eigenvalue `E λ` and `⟪ψ λ, ψ λ⟫ = 1`.
If `H` is differentiable at `l` with derivative `dH` and `ψ` is differentiable at `l` with
derivative `dψ`, then the eigenvalue function `E` is differentiable at `l` with

`dE/dλ = ⟪ψ | dH/dλ | ψ⟫`.

(The right-hand side is automatically real; we take its real part since `E` is real-valued.) -/
theorem hellmann_feynman
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (H : ℝ → F →L[ℂ] F) (dH : F →L[ℂ] F) (psi : ℝ → F) (dpsi : F) (E : ℝ → ℝ) (l : ℝ)
    (hsymm : ∀ t, ∀ x y : F, ⟪H t x, y⟫_ℂ = ⟪x, H t y⟫_ℂ)
    (hH : HasDerivAt H dH l)
    (hpsi : HasDerivAt psi dpsi l)
    (hnorm : ∀ t, ⟪psi t, psi t⟫_ℂ = 1)
    (heig : ∀ t, H t (psi t) = (E t : ℂ) • psi t) :
    HasDerivAt E (⟪psi l, dH (psi l)⟫_ℂ).re l := by
  -- the derivative of `t ↦ H t (ψ t)`
  have hK : HasDerivAt (fun t => (H t).restrictScalars ℝ) (dH.restrictScalars ℝ) l :=
    (ContinuousLinearMap.restrictScalarsL ℂ F F ℝ ℝ).hasFDerivAt.comp_hasDerivAt l hH
  have hHpsi : HasDerivAt (fun t => H t (psi t)) (dH (psi l) + H l dpsi) l := hK.clm_apply hpsi
  -- normalization forces `⟪ψ, dψ⟫ + ⟪dψ, ψ⟫ = 0`
  have hN : HasDerivAt (fun t => ⟪psi t, psi t⟫_ℂ) (⟪psi l, dpsi⟫_ℂ + ⟪dpsi, psi l⟫_ℂ) l :=
    hpsi.inner ℂ hpsi
  have hNconst : (fun t => ⟪psi t, psi t⟫_ℂ) = fun _ : ℝ => (1 : ℂ) := funext hnorm
  rw [hNconst] at hN
  have hzero : ⟪psi l, dpsi⟫_ℂ + ⟪dpsi, psi l⟫_ℂ = 0 := hN.unique (hasDerivAt_const l (1 : ℂ))
  -- the derivative of `t ↦ ⟪ψ t, H t (ψ t)⟫`
  have hG : HasDerivAt (fun t => ⟪psi t, H t (psi t)⟫_ℂ)
      (⟪psi l, dH (psi l) + H l dpsi⟫_ℂ + ⟪dpsi, H l (psi l)⟫_ℂ) l := hpsi.inner ℂ hHpsi
  -- that inner product is just `E`
  have hGE : (fun t => ⟪psi t, H t (psi t)⟫_ℂ) = fun t => ((E t : ℂ)) := by
    funext t
    rw [heig t, inner_smul_right, hnorm t, mul_one]
  -- and the derivative simplifies to `⟪ψ, dH ψ⟫`
  have hcross : ⟪psi l, H l dpsi⟫_ℂ + ⟪dpsi, H l (psi l)⟫_ℂ = 0 := by
    have h1 : ⟪psi l, H l dpsi⟫_ℂ = (E l : ℂ) * ⟪psi l, dpsi⟫_ℂ := by
      rw [← hsymm l (psi l) dpsi, heig l, inner_smul_left, Complex.conj_ofReal]
    have h2 : ⟪dpsi, H l (psi l)⟫_ℂ = (E l : ℂ) * ⟪dpsi, psi l⟫_ℂ := by
      rw [heig l, inner_smul_right]
    rw [h1, h2, ← mul_add, hzero, mul_zero]
  have hderiv : HasDerivAt (fun t => ((E t : ℂ))) (⟪psi l, dH (psi l)⟫_ℂ) l := by
    rw [hGE] at hG
    have : ⟪psi l, dH (psi l) + H l dpsi⟫_ℂ + ⟪dpsi, H l (psi l)⟫_ℂ
        = ⟪psi l, dH (psi l)⟫_ℂ := by
      rw [inner_add_right, add_assoc, hcross, add_zero]
    rwa [this] at hG
  have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt l hderiv
  simpa using this

end Phys

