import Mathlib

/-!
# Carleson
Category: Frontier Math
Target: Math2.carleson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
## Contents

`Math2.carleson` : the Fourier series of a square-integrable function on the circle
`AddCircle 1` converges to it almost everywhere.  The statement takes as an explicit hypothesis
the key intermediate result `Math2.CarlesonWeakL2 C`, the Carleson-Hunt weak `(2,2)` maximal
inequality for the Carleson maximal operator; everything else -- the density/approximation
argument by trigonometric polynomials and the passage from the maximal inequality to almost
everywhere convergence -- is proved here from scratch.

Proved unconditionally (no hypothesis) in this file:

* `Math2.tendsto_eLpNorm_partialFourierSum` : `L²` convergence of the partial Fourier sums;
* `Math2.exists_subseq_ae_tendsto_partialFourierSum` : almost everywhere convergence of a
  subsequence of the partial Fourier sums.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open MeasureTheory AddCircle Filter Topology

noncomputable section

/-- The `N`-th symmetric partial sum of the Fourier series of `f : AddCircle 1 → ℂ`. -/

theorem eventually_eLpNorm_partialFourierSum_lt (hf : MemLp f 2 haarAddCircle) {ε : ℝ≥0∞}
    (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, eLpNorm (fun x => f x - partialFourierSum f N x) 2 haarAddCircle < ε := by
  classical
  obtain ⟨e, he, hlt⟩ : ∃ e : ℝ, 0 < e ∧ ENNReal.ofReal e < ε := by
    rcases eq_or_ne ε ∞ with rfl | h
    · exact ⟨1, one_pos, by simp⟩
    · refine ⟨ε.toReal / 2, by have := ENNReal.toReal_pos hε.ne' h; linarith, ?_⟩
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_toReal h]
      simpa using ENNReal.half_lt_self hε.ne' h
  set F : Lp ℂ 2 (haarAddCircle (T := (1 : ℝ))) := hf.toLp f with hF
  have hcoeff : ∀ i, fourierCoeff (⇑F) i = fourierCoeff f i := fun i =>
    congrFun (fourierCoeff_congr_ae (hf.coeFn_toLp)) i
  have hs := hasSum_fourier_series_L2 F
  obtain ⟨s₀, hs₀⟩ := Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hs e he)
  filter_upwards [Filter.eventually_ge_atTop (s₀.sup Int.natAbs)] with N hNge
  have hsub : s₀ ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro i hi
    have hi' : i.natAbs ≤ s₀.sup Int.natAbs := Finset.le_sup hi
    simp only [Finset.mem_Icc]; omega
  have hball := hs₀ (Finset.Icc (-(N : ℤ)) (N : ℤ)) hsub
  set G : Lp ℂ 2 (haarAddCircle (T := (1 : ℝ))) :=
    ∑ i ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff (⇑F) i • fourierLp 2 i with hG
  have hGco : ⇑G =ᵐ[haarAddCircle] partialFourierSum f N := by
    filter_upwards [coeFn_trigPoly (fun i => fourierCoeff (⇑F) i)
      (Finset.Icc (-(N : ℤ)) (N : ℤ))] with x hx
    rw [hG, hx]
    simp only [partialFourierSum, hcoeff]
  have hae : (fun x => f x - partialFourierSum f N x) =ᵐ[haarAddCircle] ⇑(F - G) := by
    filter_upwards [hf.coeFn_toLp, hGco, Lp.coeFn_sub F G] with x h1 h2 h3
    rw [h3, Pi.sub_apply, h1, h2]
  rw [eLpNorm_congr_ae hae]
  have hfin : eLpNorm (⇑(F - G)) 2 haarAddCircle ≠ ∞ := Lp.eLpNorm_ne_top _
  have hnorm : ‖F - G‖ < e := by rw [← dist_eq_norm, dist_comm]; exact hball
  calc eLpNorm (⇑(F - G)) 2 haarAddCircle
      = ENNReal.ofReal ‖F - G‖ := by rw [Lp.norm_def, ENNReal.ofReal_toReal hfin]
    _ < ENNReal.ofReal e := (ENNReal.ofReal_lt_ofReal_iff he).mpr hnorm
    _ < ε := hlt

/-- There is a partial Fourier sum approximating `f` to within any prescribed `L²` accuracy. -/
