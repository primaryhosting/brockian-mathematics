/-
  RequestProject/ESA.lean

  Essential self-adjointness of the harmonic-oscillator core
  `harmonicOscillatorPMap` (the operator `-d²/dx² + x²` on the Schwartz core of
  `L²(ℝ)`).

  The argument is the classical deficiency-index one.  If `g` is in the domain of
  the adjoint with `T* g = z • g` and `Im z ≠ 0`, then pairing against the Hermite
  functions `hermiteFun n` (which lie in the Schwartz core and satisfy
  `H hermiteFun n = (2n+1) hermiteFun n`) forces `⟪g, hermiteFun n⟫ = 0` for every
  `n`, since `conj z ≠ 2n+1`.  The Hermite functions span every monomial
  `xⁿ e^{-x²/2}`, so all the moments of `x ↦ conj (g x) e^{-x²/2}` vanish, and the
  moment theorem gives `g = 0`.
-/
import RequestProject.Corpus
import RequestProject.Hermite
import RequestProject.Moments

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace

namespace Brockian.Weyl.HarmonicOscillator

open Brockian.Weyl.Operator Brockian.Weyl.SchrodingerMinimal Brockian.Moments

/-! ### Integrability facts for an `L²` function against Gaussian weights -/


theorem ae_eq_zero_of_moments_eq_zero : G =ᵐ[volume] 0 := by
  have hGint : Integrable G volume := by
    simpa using integrable_pow_mul hmeas hint 0
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hGint.locallyIntegrable ?_
  intro g hg hgsupp
  -- package `g` as a complex-valued Schwartz function
  have hsupp : HasCompactSupport (fun x : ℝ => (g x : ℂ)) :=
    hgsupp.comp_left (g := fun z : ℝ => (z : ℂ)) (by simp)
  have hdiff := Complex.ofRealCLM.contDiff.comp hg
  set phi : SchwartzMap ℝ ℂ := hsupp.toSchwartzMap hdiff with hphi
  set psi : SchwartzMap ℝ ℂ := 𝓕⁻ phi with hpsi
  have hfp : 𝓕 psi = phi := FourierTransform.fourier_fourierInv_eq phi
  have hflip : ((innerₗ ℝ).flip : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ) = innerₗ ℝ := by
    apply LinearMap.ext; intro x; apply LinearMap.ext; intro y
    exact real_inner_comm x y
  have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    Real.continuous_fourierChar (by fun_prop) hGint
    (psi.integrable (μ := (volume : Measure ℝ)))
  rw [hflip] at hswap
  replace hswap : ∫ ξ : ℝ, (𝓕 G ξ) • (psi ξ) = ∫ x : ℝ, G x • (𝓕 (⇑psi) x) := hswap
  have hzero : ∫ ξ : ℝ, (𝓕 G ξ) • (psi ξ) = 0 := by
    simp [fourier_eq_zero hmeas hint hmom]
  have hcoe : 𝓕 (⇑psi) = ⇑phi := by
    rw [← SchwartzMap.fourier_coe, hfp]
  rw [hzero, hcoe] at hswap
  have hmain : ∫ x : ℝ, G x • (phi x) = 0 := hswap.symm
  calc ∫ x : ℝ, g x • G x = ∫ x : ℝ, G x • (phi x) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        have hval : (phi : ℝ → ℂ) x = (g x : ℂ) := rfl
        show g x • G x = G x • phi x
        rw [hval, smul_eq_mul, Complex.real_smul, mul_comm]
    _ = 0 := hmain

end

end Brockian.Moments

