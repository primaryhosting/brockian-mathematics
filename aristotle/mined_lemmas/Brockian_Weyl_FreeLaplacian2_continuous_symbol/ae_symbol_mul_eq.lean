import Brockian.Weyl.FreeLaplacian2

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

/-
Essential self-adjointness of the free Laplacian on `L²(ℝᵈ)`, via the Fourier transform.
-/
import Mathlib

namespace Brockian.Weyl.FreeLaplacian2

open MeasureTheory SchwartzMap Real Function LineDeriv
open scoped FourierTransform ComplexInnerProductSpace Laplacian LinearPMap ContDiff

noncomputable section

variable (d : ℕ)

/-- The configuration space `ℝᵈ`. -/
abbrev EuclSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The Hilbert space `L²(ℝᵈ, ℂ)`. -/
abbrev L2 (d : ℕ) := Lp (α := EuclSpace d) ℂ 2

/-- The symbol of the free Laplacian: `-Δ` acts on the Fourier side as multiplication by
`4π²‖ξ‖²`. -/

theorem ae_symbol_mul_eq (y w : L2 d)
    (h : ∀ ψ : 𝓢(EuclSpace d, ℂ),
      (inner ℂ w (ψ.toLp 2 volume) : ℂ) = inner ℂ y ((mulSymbolCLM d ψ).toLp 2 volume)) :
    (fun ξ ↦ ((symbol d ξ : ℝ) : ℂ) * y ξ) =ᵐ[volume] (w : EuclSpace d → ℂ) := by
  have hyloc : LocallyIntegrable (y : EuclSpace d → ℂ) volume :=
    (MeasureTheory.Lp.memLp y).locallyIntegrable (by norm_num)
  have hwloc : LocallyIntegrable (w : EuclSpace d → ℂ) volume :=
    (MeasureTheory.Lp.memLp w).locallyIntegrable (by norm_num)
  have hmyloc : LocallyIntegrable (fun ξ ↦ ((symbol d ξ : ℝ) : ℂ) * y ξ) volume := by
    rw [← locallyIntegrableOn_univ] at hyloc ⊢
    have := hyloc.continuousOn_smul (𝕜 := ℂ) (g := fun ξ ↦ ((symbol d ξ : ℝ) : ℂ))
      isOpen_univ.isLocallyClosed
      (Continuous.continuousOn (Complex.continuous_ofReal.comp continuous_symbol))
    simpa [smul_eq_mul] using this
  refine ae_eq_of_integral_contDiff_smul_eq hmyloc hwloc ?_
  intro g hg hgsupp
  have hgC : ContDiff ℝ ∞ (fun x : EuclSpace d ↦ ((g x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hg
  have hgCsupp : HasCompactSupport (fun x : EuclSpace d ↦ ((g x : ℝ) : ℂ)) :=
    hgsupp.comp_left (g := ((↑·) : ℝ → ℂ)) Complex.ofReal_zero
  set ψ : 𝓢(EuclSpace d, ℂ) := hgCsupp.toSchwartzMap hgC
  have hψval : ∀ x, ψ x = ((g x : ℝ) : ℂ) := fun x ↦ rfl
  have hψae : ((ψ.toLp 2 (volume : Measure (EuclSpace d)) : L2 d) : EuclSpace d → ℂ)
      =ᵐ[volume] (ψ : EuclSpace d → ℂ) := ψ.coeFn_toLp 2 volume
  have hmψae : (((mulSymbolCLM d ψ).toLp 2 (volume : Measure (EuclSpace d)) : L2 d)
      : EuclSpace d → ℂ) =ᵐ[volume] ((mulSymbolCLM d ψ) : EuclSpace d → ℂ) :=
    (mulSymbolCLM d ψ).coeFn_toLp 2 volume
  have e1 : (inner ℂ w (ψ.toLp 2 (volume : Measure (EuclSpace d))) : ℂ)
      = ∫ ξ, (starRingEnd ℂ) (w ξ) * ((g ξ : ℝ) : ℂ) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hψae] with ξ hξ
    rw [RCLike.inner_apply', hξ, hψval]
  have e2 : (inner ℂ y ((mulSymbolCLM d ψ).toLp 2 (volume : Measure (EuclSpace d))) : ℂ)
      = ∫ ξ, (starRingEnd ℂ) (((symbol d ξ : ℝ) : ℂ) * y ξ) * ((g ξ : ℝ) : ℂ) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hmψae] with ξ hξ
    rw [RCLike.inner_apply', hξ, mulSymbolCLM_apply, hψval]
    simp only [map_mul, Complex.conj_ofReal]
    ring
  have key := h ψ
  rw [e1, e2] at key
  have key' := congrArg (starRingEnd ℂ) key
  rw [← integral_conj, ← integral_conj] at key'
  simp only [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply,
    Complex.conj_ofReal] at key'
  simp only [Complex.real_smul]
  have g1 : ∫ x, ((g x : ℝ) : ℂ) * (((symbol d x : ℝ) : ℂ) * y x)
      = ∫ x, ((symbol d x : ℝ) : ℂ) * y x * ((g x : ℝ) : ℂ) :=
    integral_congr_ae (Filter.Eventually.of_forall fun ξ ↦ by ring)
  have g2 : ∫ x, ((g x : ℝ) : ℂ) * (w : EuclSpace d → ℂ) x
      = ∫ x, (w : EuclSpace d → ℂ) x * ((g x : ℝ) : ℂ) :=
    integral_congr_ae (Filter.Eventually.of_forall fun ξ ↦ by ring)
  rw [g1, g2, key']

/-! ### Symmetry -/

