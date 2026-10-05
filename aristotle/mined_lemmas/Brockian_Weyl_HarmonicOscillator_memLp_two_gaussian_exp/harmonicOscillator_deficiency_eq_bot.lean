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


theorem harmonicOscillator_deficiency_eq_bot {z : ℂ} (hz : z.im ≠ 0) :
    deficiencySpace harmonicOscillatorPMap z = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro g hg
  rw [mem_deficiencySpace_iff] at hg
  have hFA := LinearPMap.adjoint_isFormalAdjoint harmonicOscillatorPMap_dense
  -- the adjoint relation, read on the Schwartz core
  have key : ∀ f : SchwartzMap ℝ ℂ,
      (starRingEnd ℂ) z * ⟪(g : L2R), schwartzToL2 f⟫_ℂ
        = ⟪(g : L2R), schwartzToL2 (oscillatorSchwartz f)⟫_ℂ := by
    intro f
    have hmem : schwartzToL2 f ∈ harmonicOscillatorPMap.domain := ⟨f, rfl⟩
    have hx : (⟨schwartzToL2 f, hmem⟩ : harmonicOscillatorPMap.domain)
        = LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f :=
      Subtype.ext (by rw [LinearEquiv.ofInjective_apply])
    have h := hFA g ⟨schwartzToL2 f, hmem⟩
    rw [hg, inner_smul_left, hx, harmonicOscillatorPMap_toFun_ofInjective,
      oscillatorCoreMap_apply] at h
    exact h
  -- the linear functional `f ↦ ⟪g, f⟫` on the Schwartz core
  set Lam : SchwartzMap ℝ ℂ →ₗ[ℂ] ℂ :=
    (innerSL ℂ (g : L2R)).toLinearMap.comp schwartzToL2 with hLam
  have hLam_apply : ∀ f : SchwartzMap ℝ ℂ, Lam f = ⟪(g : L2R), schwartzToL2 f⟫_ℂ := fun f => rfl
  -- it kills the Hermite functions
  have hherm : ∀ n : ℕ, Lam (hermiteFun n) = 0 := by
    intro n
    have h := key (hermiteFun n)
    rw [oscillator_hermiteFun n, map_smul, inner_smul_right] at h
    have hne : (starRingEnd ℂ) z ≠ (2 * n + 1 : ℂ) := by
      intro heq
      have h1 : ((starRingEnd ℂ) z).im = -z.im := Complex.conj_im z
      rw [heq] at h1
      have h2 : ((2 * (n : ℂ) + 1)).im = 0 := by simp
      rw [h2] at h1
      exact hz (by linarith)
    have hfac : ((starRingEnd ℂ) z - (2 * n + 1 : ℂ)) * ⟪(g : L2R), schwartzToL2 (hermiteFun n)⟫_ℂ
        = 0 := by
      rw [sub_mul, h, sub_self]
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) hne
    · rw [hLam_apply]; exact h1
  -- hence it kills the whole span, in particular every monomial `xⁿ e^{-x²/2}`
  have hspan : Submodule.span ℂ (Set.range hermiteFun) ≤ LinearMap.ker Lam := by
    rw [Submodule.span_le]
    rintro u ⟨n, rfl⟩
    exact hherm n
  have hpsi : ∀ n : ℕ, Lam (psiFun n) = 0 := fun n => hspan (psiFun_mem_hermiteSpan n)
  -- all moments of `G x = conj (g x) e^{-x²/2}` vanish
  set G : ℝ → ℂ := fun x => (starRingEnd ℂ) (((g : L2R) : ℝ → ℂ) x)
    * (Real.exp (-(x ^ 2 / 2)) : ℂ) with hG
  have hmom : ∀ n : ℕ, ∫ x : ℝ, (x : ℂ) ^ n * G x = 0 := by
    intro n
    have h := hpsi n
    rw [hLam_apply, inner_schwartzToL2] at h
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hG, psiFun_apply]
    ring
  have hmeasG : AEStronglyMeasurable G (volume : Measure ℝ) := by
    have h1 : AEStronglyMeasurable (fun x : ℝ => ((g : L2R) : ℝ → ℂ) x) (volume : Measure ℝ) :=
      Lp.aestronglyMeasurable (g : L2R)
    exact (Complex.continuous_conj.comp_aestronglyMeasurable h1).mul (by fun_prop)
  have hintG : ∀ c : ℝ, Integrable (fun x : ℝ => ‖G x‖ * Real.exp (c * |x|))
      (volume : Measure ℝ) := fun c => integrable_norm_mul_exp (g : L2R) c
  have hzero : G =ᵐ[volume] 0 := ae_eq_zero_of_moments_eq_zero hmeasG hintG hmom
  -- therefore `g = 0`
  have hgzero : (g : L2R) = 0 := by
    have hae : ((g : L2R) : ℝ → ℂ) =ᵐ[volume] 0 := by
      filter_upwards [hzero] with x hx
      have hexp : (Real.exp (-(x ^ 2 / 2)) : ℂ) ≠ 0 := by simp
      rcases mul_eq_zero.mp hx with h1 | h1
      · have h2 := congrArg (starRingEnd ℂ) h1
        simpa using h2
      · exact absurd h1 hexp
    exact (Lp.eq_zero_iff_ae_eq_zero).mpr hae
  exact Submodule.coe_eq_zero.mp hgzero

/-- **Essential self-adjointness of the harmonic-oscillator core.** -/
