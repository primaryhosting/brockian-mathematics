/-
# Ham Sandwich
Category: Frontier Physics
Target: Frontier.ham_sandwich
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ham Sandwich
Category: Frontier Physics
Target: Frontier.ham_sandwich
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MeasureTheory Filter Set Topology
open scoped ENNReal

/-!
## Step 1: existence of a median for a finite measure on `ℝ`

A *median* of a finite measure `ν` on `ℝ` is a point `c` such that both closed half-lines
`Iic c` and `Ici c` carry at least half of the total mass.  This is the one-dimensional
form of "bisection by a hyperplane"; it is obtained by taking `c` to be the infimum of the
set of points where the cumulative distribution function has reached half of the total mass.
-/

/-- **Existence of a median.**  Every finite measure `ν` on `ℝ` admits a point `c` such that
each of the two closed half-lines determined by `c` carries at least half of the total mass. -/

theorem exists_median (ν : Measure ℝ) [IsFiniteMeasure ν] :
    ∃ c : ℝ, ν Set.univ ≤ 2 * ν (Set.Iic c) ∧ ν Set.univ ≤ 2 * ν (Set.Ici c) := by
  by_cases hm0 : ν Set.univ = 0
  · exact ⟨0, by simp [hm0], by simp [hm0]⟩
  have h2top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hmtop : ν Set.univ ≠ ⊤ := measure_ne_top ν _
  have hmono : Monotone (fun c : ℝ => Set.Iic c) := fun a b h => Set.Iic_subset_Iic.2 h
  -- the cumulative mass tends to the total mass at `+∞` and to `0` at `-∞`
  have htop : Tendsto (fun c : ℝ => ν (Set.Iic c)) atTop (𝓝 (ν Set.univ)) := by
    have h := tendsto_measure_iUnion_atTop (μ := ν) hmono
    have he : (⋃ c : ℝ, Set.Iic c) = Set.univ := by ext x; simp
    rw [he] at h
    exact h
  have hbot : Tendsto (fun c : ℝ => ν (Set.Iic c)) atBot (𝓝 0) := by
    have h := tendsto_measure_iInter_atBot (μ := ν)
      (fun _ : ℝ => measurableSet_Iic.nullMeasurableSet) hmono ⟨0, measure_ne_top _ _⟩
    have he : (⋂ c : ℝ, Set.Iic c) = (∅ : Set ℝ) := by
      ext x
      simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false, not_forall, not_le]
      exact ⟨x - 1, by linarith⟩
    rw [he, measure_empty] at h
    exact h
  -- the set of points where at least half of the mass has accumulated
  set S := {c : ℝ | ν Set.univ ≤ 2 * ν (Set.Iic c)} with hS
  have hmemS : ∀ c : ℝ, c ∈ S ↔ ν Set.univ ≤ 2 * ν (Set.Iic c) := fun _ => Iff.rfl
  have hSup : ∀ a ∈ S, ∀ b : ℝ, a ≤ b → b ∈ S := by
    intro a ha b hab
    rw [hmemS] at ha ⊢
    refine ha.trans ?_
    gcongr
  have hSne : S.Nonempty := by
    have hlt : ν Set.univ < 2 * ν Set.univ := by
      rw [two_mul]
      exact ENNReal.lt_add_right hmtop hm0
    have h2 : Tendsto (fun c : ℝ => 2 * ν (Set.Iic c)) atTop (𝓝 (2 * ν Set.univ)) :=
      ENNReal.Tendsto.const_mul htop (Or.inr h2top)
    obtain ⟨c, hc⟩ := (h2.eventually_const_lt hlt).exists
    exact ⟨c, hc.le⟩
  have hSbdd : BddBelow S := by
    have hlt : (0 : ℝ≥0∞) < ν Set.univ := pos_iff_ne_zero.2 hm0
    have h2 : Tendsto (fun c : ℝ => 2 * ν (Set.Iic c)) atBot (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hbot (Or.inr h2top)
    obtain ⟨b, hb⟩ := eventually_atBot.1 (h2.eventually_lt_const hlt)
    refine ⟨b, fun c hc => ?_⟩
    by_contra hcb
    push_neg at hcb
    exact absurd ((hmemS c).1 hc) (not_le.2 (hb c hcb.le))
  -- the candidate median
  refine ⟨sInf S, ?_, ?_⟩
  · -- right continuity of the cumulative mass at `sInf S`
    have hanti : Antitone (fun k : ℕ => Set.Iic (sInf S + 1 / ((k : ℝ) + 1))) := by
      intro a b hab
      refine Set.Iic_subset_Iic.2 ?_
      have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      have : (1 : ℝ) / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) := by
        apply one_div_le_one_div_of_le
        · positivity
        · linarith
      linarith
    have hIic : Set.Iic (sInf S) = ⋂ k : ℕ, Set.Iic (sInf S + 1 / ((k : ℝ) + 1)) := by
      ext x
      simp only [mem_Iic, mem_iInter]
      constructor
      · intro hx k
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      · intro hx
        by_contra hlt
        push_neg at hlt
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0 : ℝ) < x - sInf S by linarith)
        have h1 := hx k
        linarith
    have hlim := tendsto_measure_iInter_atTop (μ := ν)
      (fun _ : ℕ => measurableSet_Iic.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
    rw [← hIic] at hlim
    have h2 : Tendsto (fun k : ℕ => 2 * ν (Set.Iic (sInf S + 1 / ((k : ℝ) + 1)))) atTop
        (𝓝 (2 * ν (Set.Iic (sInf S)))) := ENNReal.Tendsto.const_mul hlim (Or.inr h2top)
    refine ge_of_tendsto h2 (Filter.Eventually.of_forall fun k => ?_)
    obtain ⟨c, hcS, hc⟩ :=
      Real.lt_sInf_add_pos hSne (show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity)
    exact (hmemS _).1 (hSup c hcS _ hc.le)
  · -- everything strictly below `sInf S` carries at most half of the mass
    have hmono' : Monotone (fun k : ℕ => Set.Iic (sInf S - 1 / ((k : ℝ) + 1))) := by
      intro a b hab
      refine Set.Iic_subset_Iic.2 ?_
      have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      have : (1 : ℝ) / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) := by
        apply one_div_le_one_div_of_le
        · positivity
        · linarith
      linarith
    have hIio : Set.Iio (sInf S) = ⋃ k : ℕ, Set.Iic (sInf S - 1 / ((k : ℝ) + 1)) := by
      ext x
      simp only [mem_Iio, mem_iUnion, mem_Iic]
      constructor
      · intro hx
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0 : ℝ) < sInf S - x by linarith)
        exact ⟨k, by linarith⟩
      · rintro ⟨k, hk⟩
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    have hlim := tendsto_measure_iUnion_atTop (μ := ν) hmono'
    rw [← hIio] at hlim
    have h2 : Tendsto (fun k : ℕ => 2 * ν (Set.Iic (sInf S - 1 / ((k : ℝ) + 1)))) atTop
        (𝓝 (2 * ν (Set.Iio (sInf S)))) := ENNReal.Tendsto.const_mul hlim (Or.inr h2top)
    have hkey : 2 * ν (Set.Iio (sInf S)) ≤ ν Set.univ := by
      refine le_of_tendsto h2 (Filter.Eventually.of_forall fun k => ?_)
      have hlt : sInf S - 1 / ((k : ℝ) + 1) < sInf S := by
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      have hnot := notMem_of_lt_csInf hlt hSbdd
      rw [hmemS] at hnot
      exact (not_le.1 hnot).le
    have hsplit : ν (Set.Iio (sInf S)) + ν (Set.Ici (sInf S)) = ν Set.univ := by
      rw [← measure_add_measure_compl (measurableSet_Iio (a := sInf S))]
      simp
    have hfin : ν (Set.Iio (sInf S)) ≠ ⊤ := measure_ne_top _ _
    have hle : ν (Set.Iio (sInf S)) ≤ ν (Set.Ici (sInf S)) := by
      rw [← hsplit, two_mul] at hkey
      exact (ENNReal.add_le_add_iff_left hfin).1 hkey
    calc ν Set.univ = ν (Set.Iio (sInf S)) + ν (Set.Ici (sInf S)) := hsplit.symm
      _ ≤ ν (Set.Ici (sInf S)) + ν (Set.Ici (sInf S)) := by gcongr
      _ = 2 * ν (Set.Ici (sInf S)) := (two_mul _).symm

/-!
## Step 2: bisection of a single finite measure on `ℝⁿ` by a hyperplane
-/

/-- **Bisection of one measure.**  For every `n ≥ 1` and every finite measure `μ` on `ℝⁿ`
there is an affine hyperplane `{x | ⟪v, x⟫ = c}` (with `v ≠ 0`) such that each of the two
closed half-spaces it bounds carries at least half of the total mass of `μ`. -/
