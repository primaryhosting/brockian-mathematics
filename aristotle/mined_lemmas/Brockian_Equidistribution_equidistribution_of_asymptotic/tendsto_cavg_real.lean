import Mathlib

/-!
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
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

namespace Brockian.Equidistribution

open MeasureTheory Filter Topology Metric Finset

noncomputable section

local notation "𝕋" => AddCircle (1 : ℝ)

/-! ### Cesàro averages along a sequence -/

/-- The Cesàro average of a function `f` on the circle `ℝ/ℤ` along the first `N` terms of a
real sequence `x`. -/

lemma tendsto_cavg_real (x : ℕ → ℝ)
    (hw : ∀ h : ℤ, h ≠ 0 → Tendsto (cavg x (fourier h)) atTop (𝓝 0)) (f : C(𝕋, ℝ)) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f ((x n : ℝ) : 𝕋)) atTop
      (𝓝 (∫ z, f z)) := by
  set F : C(𝕋, ℂ) := ⟨fun z => (f z : ℂ), Complex.continuous_ofReal.comp f.continuous⟩ with hF
  have hmem : F ∈ Equidist x := by rw [equidist_eq_top x hw]; trivial
  rw [mem_equidist_iff] at hmem
  have hint : (∫ z, F z) = ((∫ z, f z : ℝ) : ℂ) := integral_complex_ofReal
  rw [hint] at hmem
  have hre := (Complex.continuous_re.tendsto _).comp hmem
  simp only [Function.comp_def, Complex.ofReal_re] at hre
  refine hre.congr (fun N => ?_)
  have hc : cavg x F N = (((N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f ((x n : ℝ) : 𝕋) : ℝ) : ℂ) := by
    simp [cavg, hF]
  rw [hc, Complex.ofReal_re]

