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

theorem meas_divergenceLimsup_eq_zero {C : ℝ≥0∞} (hC : C ≠ ∞) (hbound : CarlesonWeakL2 C)
    {f : AddCircle (1 : ℝ) → ℂ} (hf : MemLp f 2 haarAddCircle) {lam : ℝ≥0∞} (hlam : lam ≠ 0) :
    haarAddCircle {x | lam < divergenceLimsup f x} = 0 := by
  set L : ℝ≥0∞ := (lam / 2) ^ 2 with hL
  have hLne : L ≠ 0 := by
    have h : lam / 2 ≠ 0 := by simp [ENNReal.div_eq_zero_iff, hlam]
    simp [hL, h]
  set K : ℝ≥0∞ := (C + 1) * L⁻¹ with hK
  have hKne : K ≠ ∞ := by
    apply ENNReal.mul_ne_top (by finiteness)
    simpa using hLne
  have hbdd : ∀ n : ℕ, 1 ≤ n →
      haarAddCircle {x | lam < divergenceLimsup f x} ≤ K * (n : ℝ≥0∞)⁻¹ := by
    intro n hn
    have hεpos : (0 : ℝ≥0∞) < (n : ℝ≥0∞)⁻¹ := by simp [ENNReal.inv_pos]
    refine (meas_divergenceLimsup_le hbound hf hlam hεpos).trans ?_
    have hle : ((n : ℝ≥0∞)⁻¹) ^ 2 ≤ (n : ℝ≥0∞)⁻¹ := by
      have h1 : (n : ℝ≥0∞)⁻¹ ≤ 1 := by
        rw [ENNReal.inv_le_one]; exact_mod_cast hn
      calc ((n : ℝ≥0∞)⁻¹) ^ 2 = (n : ℝ≥0∞)⁻¹ * (n : ℝ≥0∞)⁻¹ := sq _
        _ ≤ (n : ℝ≥0∞)⁻¹ * 1 := by gcongr
        _ = (n : ℝ≥0∞)⁻¹ := mul_one _
    calc (C + 1) * ((n : ℝ≥0∞)⁻¹) ^ 2 / L = K * ((n : ℝ≥0∞)⁻¹) ^ 2 := by
          rw [hK, ENNReal.div_eq_inv_mul]; ring
      _ ≤ K * (n : ℝ≥0∞)⁻¹ := by gcongr
  have htend : Tendsto (fun n : ℕ => K * (n : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (a := K) (b := (0 : ℝ≥0∞))
      ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hKne)
  refine le_antisymm (ge_of_tendsto htend ?_) (zero_le _)
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn using hbdd n hn

/-- If the `limsup` of the distances vanishes at `x`, the Fourier series converges at `x`. -/
