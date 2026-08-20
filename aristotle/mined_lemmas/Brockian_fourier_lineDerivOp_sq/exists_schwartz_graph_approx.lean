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

import Mathlib

/-!
# The Fourier transform of the Laplacian on Schwartz space

We record the classical formula `𝓕 (Δ f) ξ = -(4π²‖ξ‖²) 𝓕 f ξ` for Schwartz functions,
introduce the Fourier symbol `freeSymbol ξ = 4π²‖ξ‖²` of the free Laplacian `-Δ`, and show that
the "resolvent multiplier" `ξ ↦ (1 + freeSymbol ξ)⁻¹` has temperate growth (so that multiplying
a Schwartz function by it produces again a Schwartz function).
-/

namespace Brockian

open MeasureTheory SchwartzMap Real LineDeriv
open scoped FourierTransform SchwartzMap ComplexInnerProductSpace

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]


theorem exists_schwartz_graph_approx (u : (freeLaplacian (V := V)).domain) :
    ∃ f : ℕ → 𝓢(V, ℂ),
      Tendsto (fun k => (schwartzToL2 (f k) : L2 V)) atTop (𝓝 (u : L2 V)) ∧
      Tendsto (fun k => (schwartzToL2 (negLaplacianSchwartz (f k)) : L2 V)) atTop
        (𝓝 (freeLaplacian u : L2 V)) := by
  have hu : fourierU V (u : L2 V) ∈ (mulOp (freeSymbol : V → ℝ)).domain := u.2
  set ghat : L2 V := fourierU V (u : L2 V) with hghat_def
  set W : L2 V := mulOp (freeSymbol : V → ℝ) ⟨ghat, hu⟩ with hW_def
  have hWae : ((W : L2 V) : V → ℂ) =ᵐ[volume] fun x => (freeSymbol x : ℂ) * ((ghat : L2 V) : V → ℂ) x :=
    coeFn_mulOp _ _
  have hLu : (freeLaplacian u : L2 V) = (fourierU V).symm W := conjPMap_apply _ _ u hu
  have husymm : ((fourierU V).symm ghat : L2 V) = (u : L2 V) := by
    rw [hghat_def, LinearIsometryEquiv.symm_apply_apply]
  obtain ⟨psi, hpsi⟩ := exists_schwartz_tendsto (ghat + W)
  have hrT : Function.HasTemperateGrowth (freeResolventSymbol : V → ℂ) :=
    hasTemperateGrowth_freeResolventSymbol
  set phi : ℕ → 𝓢(V, ℂ) := fun k => smulLeftCLM ℂ (freeResolventSymbol : V → ℂ) (psi k)
    with hphi_def
  have hphi_apply : ∀ k x, phi k x = freeResolventSymbol x * psi k x := by
    intro k x
    rw [hphi_def]
    simpa using smulLeftCLM_apply_apply hrT (psi k) x
  set chi : ℕ → 𝓢(V, ℂ) := fun k => 𝓕 (negLaplacianSchwartz (𝓕⁻ (phi k))) with hchi_def
  have hchi_apply : ∀ k x, chi k x = (freeSymbol x : ℂ) * phi k x := by
    intro k x
    rw [hchi_def]
    simp only [negLaplacianSchwartz_apply]
    rw [fourier_neg_laplacian, FourierTransform.fourier_fourierInv_eq]
  -- the two pointwise identities relating `ghat`, `W` and their sum
  have hkey1 : ∀ᵐ x ∂(volume : Measure V),
      freeResolventSymbol x * ((ghat + W : L2 V) : V → ℂ) x = ((ghat : L2 V) : V → ℂ) x := by
    filter_upwards [hWae, Lp.coeFn_add ghat W] with x h1 h2
    have hpos := one_add_freeSymbol_pos (V := V) x
    have hne : (1 + (freeSymbol x : ℂ)) ≠ 0 := by
      have : ((1 + freeSymbol x : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
      push_cast at this
      exact this
    rw [h2]
    simp only [Pi.add_apply, h1, freeResolventSymbol]
    push_cast
    field_simp
  have hkey2 : ∀ᵐ x ∂(volume : Measure V),
      (freeSymbol x : ℂ) * freeResolventSymbol x * ((ghat + W : L2 V) : V → ℂ) x
        = ((W : L2 V) : V → ℂ) x := by
    filter_upwards [hkey1, hWae] with x h1 h2
    rw [mul_assoc, h1, h2]
  -- the two norm estimates
  have hest1 : ∀ k, ‖(schwartzToL2 (phi k) : L2 V) - ghat‖
      ≤ ‖(schwartzToL2 (psi k) : L2 V) - (ghat + W)‖ := by
    intro k
    have hb : ∀ᵐ x ∂(volume : Measure V), ‖(freeResolventSymbol x : ℂ)‖ ≤ 1 :=
      Filter.Eventually.of_forall (norm_freeResolventSymbol_le_one (V := V))
    have hae : (((schwartzToL2 (phi k) : L2 V) - ghat : L2 V) : V → ℂ)
        =ᵐ[volume] fun x => freeResolventSymbol x *
          (((schwartzToL2 (psi k) : L2 V) - (ghat + W) : L2 V) : V → ℂ) x := by
      filter_upwards [Lp.coeFn_sub (schwartzToL2 (phi k) : L2 V) ghat,
        Lp.coeFn_sub (schwartzToL2 (psi k) : L2 V) (ghat + W),
        coeFn_schwartzToL2 (phi k), coeFn_schwartzToL2 (psi k), hkey1] with x h1 h2 h3 h4 h5
      rw [h1, h2]
      simp only [Pi.sub_apply] at *
      rw [h3, h4, hphi_apply k x, mul_sub, h5]
    simpa using norm_le_of_ae_mul zero_le_one hb hae
  have hest2 : ∀ k, ‖(schwartzToL2 (chi k) : L2 V) - W‖
      ≤ ‖(schwartzToL2 (psi k) : L2 V) - (ghat + W)‖ := by
    intro k
    have hb : ∀ᵐ x ∂(volume : Measure V),
        ‖(freeSymbol x : ℂ) * freeResolventSymbol x‖ ≤ 1 :=
      Filter.Eventually.of_forall (norm_freeSymbol_mul_freeResolventSymbol_le_one (V := V))
    have hae : (((schwartzToL2 (chi k) : L2 V) - W : L2 V) : V → ℂ)
        =ᵐ[volume] fun x => ((freeSymbol x : ℂ) * freeResolventSymbol x) *
          (((schwartzToL2 (psi k) : L2 V) - (ghat + W) : L2 V) : V → ℂ) x := by
      filter_upwards [Lp.coeFn_sub (schwartzToL2 (chi k) : L2 V) W,
        Lp.coeFn_sub (schwartzToL2 (psi k) : L2 V) (ghat + W),
        coeFn_schwartzToL2 (chi k), coeFn_schwartzToL2 (psi k), hkey2] with x h1 h2 h3 h4 h5
      rw [h1, h2]
      simp only [Pi.sub_apply] at *
      rw [h3, h4, hchi_apply k x, hphi_apply k x, mul_sub, h5, mul_assoc]
    simpa using norm_le_of_ae_mul zero_le_one hb hae
  have hA : Tendsto (fun k => (schwartzToL2 (phi k) : L2 V)) atTop (𝓝 ghat) :=
    tendsto_of_norm_sub_le hest1 hpsi
  have hB : Tendsto (fun k => (schwartzToL2 (chi k) : L2 V)) atTop (𝓝 W) :=
    tendsto_of_norm_sub_le hest2 hpsi
  refine ⟨fun k => 𝓕⁻ (phi k), ?_, ?_⟩
  · have h := ((fourierU V).symm.continuous.tendsto ghat).comp hA
    rw [husymm] at h
    refine h.congr (fun k => ?_)
    simp only [Function.comp_apply]
    exact fourierU_symm_schwartzToL2 (phi k)
  · have h := ((fourierU V).symm.continuous.tendsto W).comp hB
    rw [← hLu] at h
    refine h.congr (fun k => ?_)
    have hne : 𝓕⁻ (chi k) = negLaplacianSchwartz (𝓕⁻ (phi k)) := by
      rw [hchi_def]
      exact FourierTransform.fourierInv_fourier_eq _
    simp only [Function.comp_apply]
    rw [fourierU_symm_schwartzToL2 (chi k), hne]

