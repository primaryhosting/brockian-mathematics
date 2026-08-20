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

theorem meas_divergenceLimsup_le {C : ℝ≥0∞} (hbound : CarlesonWeakL2 C)
    {f : AddCircle (1 : ℝ) → ℂ} (hf : MemLp f 2 haarAddCircle) {lam : ℝ≥0∞} (hlam : lam ≠ 0)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    haarAddCircle {x | lam < divergenceLimsup f x} ≤ (C + 1) * ε ^ 2 / (lam / 2) ^ 2 := by
  obtain ⟨N₀, hN₀⟩ := exists_eLpNorm_partialFourierSum_lt hf hε
  set P := partialFourierSum f N₀ with hP
  set g : AddCircle (1 : ℝ) → ℂ := fun x => f x - P x with hg
  have hfint : Integrable f haarAddCircle := hf.integrable (by norm_num)
  have hPint : Integrable P haarAddCircle := integrable_partialFourierSum f N₀
  have hgmem : MemLp g 2 haarAddCircle := hf.sub (memLp_partialFourierSum f N₀)
  have hptwise : ∀ x, divergenceLimsup f x ≤ carlesonOperator g x + ‖g x‖ₑ := by
    intro x
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
    have h1 : partialFourierSum g N x = partialFourierSum f N x - P x := by
      rw [hg, partialFourierSum_sub hfint hPint N x, hP,
        partialFourierSum_partialFourierSum f hN]
    have h2 : partialFourierSum f N x - f x = partialFourierSum g N x - g x := by
      rw [h1, hg]; ring
    calc ‖partialFourierSum f N x - f x‖ₑ = ‖partialFourierSum g N x - g x‖ₑ := by rw [h2]
      _ ≤ ‖partialFourierSum g N x‖ₑ + ‖g x‖ₑ := enorm_sub_le
      _ ≤ carlesonOperator g x + ‖g x‖ₑ := by
          gcongr
          exact enorm_partialFourierSum_le_carlesonOperator g N x
  have hsubset : {x | lam < divergenceLimsup f x} ⊆
      {x | lam / 2 < carlesonOperator g x} ∪ {x | lam / 2 < ‖g x‖ₑ} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hcon
    have hle := (hptwise x).trans (add_le_add hcon.1 hcon.2)
    rw [ENNReal.add_halves] at hle
    exact absurd (lt_of_lt_of_le hx hle) (lt_irrefl _)
  have hhalf : lam / 2 ≠ 0 := by simp [ENNReal.div_eq_zero_iff, hlam]
  calc haarAddCircle {x | lam < divergenceLimsup f x}
      ≤ haarAddCircle ({x | lam / 2 < carlesonOperator g x} ∪ {x | lam / 2 < ‖g x‖ₑ}) :=
        measure_mono hsubset
    _ ≤ haarAddCircle {x | lam / 2 < carlesonOperator g x}
          + haarAddCircle {x | lam / 2 < ‖g x‖ₑ} := measure_union_le _ _
    _ ≤ C * eLpNorm g 2 haarAddCircle ^ 2 / (lam / 2) ^ 2
          + eLpNorm g 2 haarAddCircle ^ 2 / (lam / 2) ^ 2 :=
        add_le_add (hbound g hgmem (lam / 2) hhalf) (meas_lt_enorm_le g hgmem hhalf)
    _ = (C + 1) * eLpNorm g 2 haarAddCircle ^ 2 / (lam / 2) ^ 2 := by
        rw [ENNReal.div_add_div_same, add_mul, one_mul]
    _ ≤ (C + 1) * ε ^ 2 / (lam / 2) ^ 2 := by gcongr

/-- Consequently, for each fixed threshold the exceptional set is null. -/
