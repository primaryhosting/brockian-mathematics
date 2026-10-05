/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open MeasureTheory Filter Topology Set

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

lemma tendsto_empiricalProb_of_counting (θ : ℕ → ℝ) (hmem : ∀ p, θ p ∈ Icc 0 Real.pi)
    (h : SatoTateCounting θ) : Tendsto (empiricalProb θ) atTop (𝓝 satoTateProb) := by
  have key : ∀ a b : ℝ, Tendsto (fun X => (empirical θ X).real (Ioo a b)) atTop
      (𝓝 (satoTateMeasure.real (Ioo a b))) := by
    intro a b
    obtain ⟨α, β, hα, hαβ, hβ, hsub, hsup⟩ := exists_Icc_squeeze a b
    have hIcc : Tendsto (fun X => (empirical θ X).real (Icc α β)) atTop
        (𝓝 (satoTateMeasure.real (Icc α β))) := by
      rw [satoTate_Icc hα hαβ hβ]
      refine (h α β hα hαβ hβ).congr' ?_
      filter_upwards [eventually_ge_atTop 3] with X hX
      rw [empirical_real θ (card_primesBelow_ne_zero hX) measurableSet_Icc]
      rfl
    have hatoms : Tendsto (fun X => (empirical θ X).real {α} + (empirical θ X).real {β})
        atTop (𝓝 0) := by
      have := (tendsto_primeRatio_singleton θ h hα (hαβ.trans hβ)).add
        (tendsto_primeRatio_singleton θ h (hα.trans hαβ) hβ)
      simpa using this
    -- the empirical measure of `Ioo a b` differs from that of `Icc α β` by at most the atoms
    have hd : ∀ X, |(empirical θ X).real (Ioo a b) - (empirical θ X).real (Icc α β)| ≤
        (empirical θ X).real {α} + (empirical θ X).real {β} := by
      intro X
      have h1 : (empirical θ X).real (Ioo a b) = (empirical θ X).real (Ioo a b ∩ Icc 0 Real.pi) :=
        empirical_real_inter_Icc θ hmem X measurableSet_Ioo
      have hle1 : (empirical θ X).real (Ioo a b) ≤ (empirical θ X).real (Icc α β) := by
        rw [h1]; exact measureReal_mono hsub
      have hle2 : (empirical θ X).real (Icc α β) ≤ (empirical θ X).real (Ioo a b)
          + ((empirical θ X).real {α} + (empirical θ X).real {β}) := by
        calc (empirical θ X).real (Icc α β)
            ≤ (empirical θ X).real ((Ioo a b ∩ Icc 0 Real.pi) ∪ {α, β}) := measureReal_mono hsup
          _ ≤ (empirical θ X).real (Ioo a b ∩ Icc 0 Real.pi)
              + (empirical θ X).real ({α, β} : Set ℝ) := measureReal_union_le _ _
          _ ≤ (empirical θ X).real (Ioo a b)
              + ((empirical θ X).real {α} + (empirical θ X).real {β}) := by
              rw [h1]
              have : (({α, β} : Set ℝ)) = {α} ∪ {β} := rfl
              gcongr
              rw [this]
              exact measureReal_union_le _ _
      rw [abs_sub_le_iff]
      constructor <;> linarith
    have hST : satoTateMeasure.real (Ioo a b) = satoTateMeasure.real (Icc α β) := by
      have h1 : satoTateMeasure (Ioo a b) = satoTateMeasure (Ioo a b ∩ Icc 0 Real.pi) :=
        satoTate_inter_Icc measurableSet_Ioo
      have hle1 : satoTateMeasure (Ioo a b) ≤ satoTateMeasure (Icc α β) := by
        rw [h1]; exact measure_mono hsub
      have hle2 : satoTateMeasure (Icc α β) ≤ satoTateMeasure (Ioo a b) := by
        calc satoTateMeasure (Icc α β)
            ≤ satoTateMeasure ((Ioo a b ∩ Icc 0 Real.pi) ∪ {α, β}) := measure_mono hsup
          _ ≤ satoTateMeasure (Ioo a b ∩ Icc 0 Real.pi) + satoTateMeasure ({α, β} : Set ℝ) :=
              measure_union_le _ _
          _ = satoTateMeasure (Ioo a b) := by
              rw [← h1]
              have : satoTateMeasure ({α, β} : Set ℝ) = 0 :=
                measure_union_null (satoTate_singleton α) (satoTate_singleton β)
              rw [this, add_zero]
      rw [measureReal_def, measureReal_def, le_antisymm hle1 hle2]
    rw [hST]
    have hzero : Tendsto
        (fun X => (empirical θ X).real (Ioo a b) - (empirical θ X).real (Icc α β)) atTop (𝓝 0) :=
      squeeze_zero_norm (fun X => by simpa only [Real.norm_eq_abs] using hd X) hatoms
    simpa using hzero.add hIcc
  refine IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem
    (S := {s : Set ℝ | ∃ a b : ℝ, s = Ioo a b}) ?_ ?_ ?_ ?_
  · rintro s ⟨a, b, rfl⟩ t ⟨c, d, rfl⟩ -
    exact ⟨max a c, min b d, by rw [Set.Ioo_inter_Ioo]⟩
  · rintro s ⟨a, b, rfl⟩
    exact measurableSet_Ioo
  · intro u hu x hx
    obtain ⟨a, b, hab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hu.mem_nhds hx)
    exact ⟨Ioo a b, ⟨a, b, rfl⟩, Ioo_mem_nhds hab.1 hab.2, hsub⟩
  · rintro s ⟨a, b, rfl⟩
    have hkey := key a b
    rw [← NNReal.tendsto_coe]
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn, empiricalProb_toMeasure,
      satoTateProb_toMeasure] using hkey

/-- The two forms of the Sato–Tate law agree, for a sequence of angles taking values in `[0, π]`:
weak convergence of the empirical distributions is equivalent to the classical statement about
the densities of primes whose angle lies in a given subinterval of `[0, π]`. -/
