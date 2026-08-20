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
/-!
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

open MeasureTheory SchwartzMap FourierTransform Complex
open scoped ComplexInnerProductSpace

namespace Brockian.FreeLaplacianPlancherel

/-! ## Abstract theory of graphs of unbounded operators -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The graph of the adjoint of the (not necessarily bounded) operator whose graph is `G`:
the set of pairs `(g, h)` with `⟪T f, g⟫ = ⟪f, h⟫` for all `(f, T f) ∈ G`. -/

lemma orthogonal_shift_eq_zero (z : ℂ) (hz : z.im ≠ 0) (w : L2R)
    (h : ∀ p ∈ freeLaplacianGraph, ⟪p.2 + z • p.1, w⟫ = 0) : w = 0 := by
  set u : L2R := 𝓕 w with hu
  -- Step 1: on the Fourier side the hypothesis says that `(m + conj z) * u` kills every
  -- Schwartz test function.
  have key : ∀ φ : 𝓢(ℝ, ℂ), ∫ x : ℝ, (starRingEnd ℂ) (φ x) *
      ((((laplacianSymbol x : ℝ) : ℂ) + (starRingEnd ℂ) z) * (u x)) = 0 := by
    intro φ
    obtain ⟨f, hf⟩ : ∃ f : 𝓢(ℝ, ℂ), (𝓕 f : 𝓢(ℝ, ℂ)) = φ :=
      ⟨𝓕⁻ φ, fourier_fourierInv_eq φ⟩
    have h0 := h _ (mem_freeLaplacianGraph f)
    simp only at h0
    rw [← MeasureTheory.Lp.inner_fourier_eq (toL2 (freeLaplacian f) + z • toL2 f) w,
      FourierAdd.fourier_add, fourier_smul, fourier_toL2, fourier_toL2, ← map_smul toL2 z,
      ← map_add, inner_toL2] at h0
    rw [← h0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [SchwartzMap.add_apply, SchwartzMap.smul_apply, fourier_freeLaplacian, hf, smul_eq_mul]
    simp only [map_add, map_mul, Complex.conj_ofReal]
    ring
  -- Step 2: hence `(m + conj z) * u = 0` almost everywhere.
  have hcont : Continuous fun x : ℝ => (((laplacianSymbol x : ℝ) : ℂ) + (starRingEnd ℂ) z) := by
    unfold laplacianSymbol
    fun_prop
  have hloc : LocallyIntegrable
      (fun x : ℝ => (((laplacianSymbol x : ℝ) : ℂ) + (starRingEnd ℂ) z) * (u x)) volume :=
    locallyIntegrable_mul_of_continuous hcont
      ((MeasureTheory.Lp.memLp u).locallyIntegrable one_le_two)
  have hae : ∀ᵐ x : ℝ ∂volume,
      (((laplacianSymbol x : ℝ) : ℂ) + (starRingEnd ℂ) z) * (u x) = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun χ hχ hχc => ?_
    have hsm : ContDiff ℝ (⊤ : ℕ∞) (Complex.ofRealCLM ∘ χ) := Complex.ofRealCLM.contDiff.comp hχ
    have hcs : HasCompactSupport (Complex.ofRealCLM ∘ χ) := hχc.comp_left rfl
    rw [← key (hcs.toSchwartzMap hsm)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp
  -- Step 3: `m x + conj z` never vanishes, so `u = 0` and therefore `w = 0`.
  have hu0 : u = 0 := by
    rw [MeasureTheory.Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [hae] with x hx
    rcases mul_eq_zero.1 hx with h1 | h2
    · exfalso
      apply hz
      have := congrArg Complex.im h1
      simpa using this
    · exact h2
  have hnorm : ‖w‖ = 0 := by
    rw [← MeasureTheory.Lp.norm_fourier_eq w, ← hu, hu0, norm_zero]
  exact norm_eq_zero.1 hnorm

/-! ### The main theorem -/

/-- **The free Laplacian is essentially self-adjoint on the Schwartz space**, proved via
Plancherel's theorem: the Fourier transform is unitary on `L²(ℝ, ℂ)` and turns `-d²/dx²` into
multiplication by `4π²ξ²`, so the ranges of `T ± i` are dense and the basic criterion applies.
The statement records that the domain (the Schwartz space) is dense, that the operator is
symmetric, and that the graph of its adjoint is exactly the closure of its graph. -/
