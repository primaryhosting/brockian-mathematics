/-
# Hellmann Feynman
Category: Frontier Phys
Target: Phys.hellmann_feynman
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Phys

/-- **Hellmann–Feynman theorem.**

Let `H : ℝ → (V →L[ℂ] V)` be a family of operators on a complex inner product space,
depending on a parameter `t`, and let `ψ t` be a normalized eigenvector of `H t` with
(real) eigenvalue `E t`.  If `H` and `ψ` are differentiable at `l` and `H l` is
self-adjoint, then

`dE/dt (l) = ⟪ψ l, (dH/dt (l)) (ψ l)⟫`.

(The right-hand side is a real number: we take its real part, which is the whole of it
whenever `dH/dt` is self-adjoint.) -/
theorem hellmann_feynman
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (H : ℝ → V →L[ℂ] V) (ψ : ℝ → V) (E : ℝ → ℝ) (l : ℝ)
    (Hd : V →L[ℂ] V) (ψd : V)
    (hH : HasDerivAt H Hd l) (hψ : HasDerivAt ψ ψd l)
    (hnorm : ∀ t, inner ℂ (ψ t) (ψ t) = (1 : ℂ))
    (hEig : ∀ t, H t (ψ t) = (E t : ℂ) • ψ t)
    (hsa : ∀ x y, inner ℂ (H l x) y = inner ℂ x (H l y)) :
    HasDerivAt E (inner ℂ (ψ l) (Hd (ψ l))).re l := by
  -- The application `t ↦ H t (ψ t)` is differentiable, with the expected derivative.
  have hR : HasDerivAt (fun t => (H t).restrictScalars ℝ)
      (Hd.restrictScalars ℝ) l :=
    (ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ).hasFDerivAt.comp_hasDerivAt l hH
  have happ : HasDerivAt (fun t => H t (ψ t)) (Hd (ψ l) + H l ψd) l := by
    simpa using hR.clm_apply hψ
  -- Differentiate `t ↦ ⟪ψ t, H t (ψ t)⟫`.
  have hF : HasDerivAt (fun t => inner ℂ (ψ t) (H t (ψ t)))
      (inner ℂ (ψ l) (Hd (ψ l) + H l ψd) + inner ℂ ψd (H l (ψ l))) l :=
    hψ.inner ℂ happ
  -- Normalization forces `⟪ψ l, ψd⟫ + ⟪ψd, ψ l⟫ = 0`.
  have hnn : HasDerivAt (fun t => inner ℂ (ψ t) (ψ t))
      (inner ℂ (ψ l) ψd + inner ℂ ψd (ψ l)) l := hψ.inner ℂ hψ
  have hzero : (inner ℂ (ψ l) ψd : ℂ) + inner ℂ ψd (ψ l) = 0 := by
    have hc : HasDerivAt (fun t => inner ℂ (ψ t) (ψ t)) (0 : ℂ) l := by
      simp only [hnorm]
      exact hasDerivAt_const l (1 : ℂ)
    exact hnn.unique hc
  -- The cross terms cancel, using the eigenvalue equation and self-adjointness.
  have hcross : (inner ℂ (ψ l) (H l ψd) : ℂ) + inner ℂ ψd (H l (ψ l)) = 0 := by
    have h1 : (inner ℂ (ψ l) (H l ψd) : ℂ) = (E l : ℂ) * inner ℂ (ψ l) ψd := by
      rw [← hsa (ψ l) ψd, hEig l, inner_smul_left, Complex.conj_ofReal]
    have h2 : (inner ℂ ψd (H l (ψ l)) : ℂ) = (E l : ℂ) * inner ℂ ψd (ψ l) := by
      rw [hEig l, inner_smul_right]
    rw [h1, h2, ← mul_add, hzero, mul_zero]
  -- Hence the derivative of `t ↦ ⟪ψ t, H t (ψ t)⟫` is `⟪ψ l, Hd (ψ l)⟫`.
  have hF' : HasDerivAt (fun t => inner ℂ (ψ t) (H t (ψ t)))
      (inner ℂ (ψ l) (Hd (ψ l))) l := by
    have : (inner ℂ (ψ l) (Hd (ψ l) + H l ψd) : ℂ) + inner ℂ ψd (H l (ψ l))
        = inner ℂ (ψ l) (Hd (ψ l)) := by
      rw [inner_add_right, add_assoc, hcross, add_zero]
    rwa [this] at hF
  -- But that function is just `E` (as a complex number).
  have hE : HasDerivAt (fun t => ((E t : ℝ) : ℂ)) (inner ℂ (ψ l) (Hd (ψ l))) l := by
    have hfun : (fun t => inner ℂ (ψ t) (H t (ψ t))) = fun t => ((E t : ℝ) : ℂ) := by
      funext t
      rw [hEig t, inner_smul_right, hnorm t, mul_one]
    rwa [hfun] at hF'
  simpa using Complex.reCLM.hasFDerivAt.comp_hasDerivAt l hE

/-- The Hellmann–Feynman theorem, phrased with `deriv`. -/
theorem hellmann_feynman_deriv
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (H : ℝ → V →L[ℂ] V) (ψ : ℝ → V) (E : ℝ → ℝ) (l : ℝ)
    (Hd : V →L[ℂ] V) (ψd : V)
    (hH : HasDerivAt H Hd l) (hψ : HasDerivAt ψ ψd l)
    (hnorm : ∀ t, inner ℂ (ψ t) (ψ t) = (1 : ℂ))
    (hEig : ∀ t, H t (ψ t) = (E t : ℂ) • ψ t)
    (hsa : ∀ x y, inner ℂ (H l x) y = inner ℂ x (H l y)) :
    deriv E l = (inner ℂ (ψ l) (Hd (ψ l))).re :=
  (hellmann_feynman H ψ E l Hd ψd hH hψ hnorm hEig hsa).deriv

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

