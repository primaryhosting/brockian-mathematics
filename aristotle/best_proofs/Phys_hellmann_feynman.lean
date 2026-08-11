import Mathlib

/-!
# Hellmann Feynman
Category: Frontier Phys
Target: Phys.hellmann_feynman
Statement: dE_n/dλ = ⟨ψ_n|∂H/∂λ|ψ_n⟩ (Hellmann–Feynman).
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

set_option grind.warning false

namespace Phys

/-- **Hellmann–Feynman theorem.**

Let `V` be a complex inner product space and let `Hm : ℝ → V →L[ℂ] V` be a family of
operators depending on a parameter `λ`, with `psi λ` a normalized eigenvector of `Hm λ`
with real eigenvalue `en λ`.  If `Hm`, `psi` and `en` are differentiable at `lam`
(with derivatives `dH`, `dpsi`, `den`) and `Hm lam` is symmetric, then

`dE_n/dλ = ⟪ψ_n, (∂H/∂λ) ψ_n⟫`,

i.e. `den = ⟪psi lam, dH (psi lam)⟫`. -/
theorem hellmann_feynman
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {Hm : ℝ → V →L[ℂ] V} {dH : V →L[ℂ] V} {psi : ℝ → V} {dpsi : V}
    {en : ℝ → ℝ} {den lam : ℝ}
    (hH : HasDerivAt Hm dH lam)
    (hpsi : HasDerivAt psi dpsi lam)
    (hen : HasDerivAt en den lam)
    (hnorm : inner ℂ (psi lam) (psi lam) = (1 : ℂ))
    (hsymm : ∀ y z : V, inner ℂ (Hm lam y) z = inner ℂ y (Hm lam z))
    (heig : ∀ x, Hm x (psi x) = (en x : ℂ) • psi x) :
    (den : ℂ) = inner ℂ (psi lam) (dH (psi lam)) := by
  set p := psi lam with hp
  -- The family of operators, viewed as `ℝ`-linear maps, is differentiable at `lam`.
  have hR : HasDerivAt (fun x => (Hm x).restrictScalars ℝ) (dH.restrictScalars ℝ) lam :=
    (ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ).hasFDerivAt.comp_hasDerivAt lam hH
  have happ : HasDerivAt (fun x => Hm x (psi x)) (dH p + Hm lam dpsi) lam := hR.clm_apply hpsi
  -- Differentiate `x ↦ ⟪ψ(lam), H(x) ψ(x)⟫` in two ways.
  have h1 : HasDerivAt (fun x => inner ℂ p (Hm x (psi x)))
      (inner ℂ p (dH p + Hm lam dpsi) + inner ℂ (0 : V) (Hm lam (psi lam))) lam :=
    (hasDerivAt_const lam p).inner ℂ happ
  have hinner : HasDerivAt (fun x => inner ℂ p (psi x)) (inner ℂ p dpsi) lam := by
    have := (hasDerivAt_const lam p).inner ℂ hpsi
    simpa using this
  have h2 : HasDerivAt (fun x => (en x : ℂ) * inner ℂ p (psi x))
      ((den : ℂ) * inner ℂ p p + (en lam : ℂ) * inner ℂ p dpsi) lam := by
    have := (hen.ofReal_comp (z := lam)).mul hinner
    simpa only [Pi.mul_apply] using this
  have hfun : (fun x => inner ℂ p (Hm x (psi x))) = fun x => (en x : ℂ) * inner ℂ p (psi x) := by
    funext x
    rw [heig x, inner_smul_right]
  rw [hfun] at h1
  have key := h2.unique h1
  -- Symmetry of `H(lam)` kills the term involving `dpsi`.
  have heigp : Hm lam p = (en lam : ℂ) • p := heig lam
  have hsym2 : inner ℂ p (Hm lam dpsi) = (en lam : ℂ) * inner ℂ p dpsi := by
    rw [← hsymm p dpsi, heigp, inner_smul_left]
    simp
  rw [inner_add_right, hsym2, hnorm, inner_zero_left, mul_one, add_zero] at key
  linear_combination key

/-- **Hellmann–Feynman theorem**, stated with the normalization `‖ψ_n‖ = 1` and with the
real-valued conclusion `dE_n/dλ = re ⟪ψ_n, (∂H/∂λ) ψ_n⟫`. -/
theorem hellmann_feynman_of_norm_one
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {Hm : ℝ → V →L[ℂ] V} {dH : V →L[ℂ] V} {psi : ℝ → V} {dpsi : V}
    {en : ℝ → ℝ} {den lam : ℝ}
    (hH : HasDerivAt Hm dH lam)
    (hpsi : HasDerivAt psi dpsi lam)
    (hen : HasDerivAt en den lam)
    (hnorm : ‖psi lam‖ = 1)
    (hsymm : ∀ y z : V, inner ℂ (Hm lam y) z = inner ℂ y (Hm lam z))
    (heig : ∀ x, Hm x (psi x) = (en x : ℂ) • psi x) :
    den = (inner ℂ (psi lam) (dH (psi lam)) : ℂ).re := by
  have hnorm' : inner ℂ (psi lam) (psi lam) = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]; norm_num
  have := hellmann_feynman hH hpsi hen hnorm' hsymm heig
  rw [← this, Complex.ofReal_re]

end Phys

