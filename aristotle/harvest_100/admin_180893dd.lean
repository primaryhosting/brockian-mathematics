/-
# Ham Sandwich
Category: Frontier Physics
Target: Frontier.ham_sandwich
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

open MeasureTheory Set Filter Topology

/-! ## A median for a finite measure on the real line -/

/-- Every finite Borel measure on `ℝ` admits a median: a point `c` such that both open
half-lines determined by `c` carry at most half of the total mass. -/
theorem exists_median (ν : Measure ℝ) [IsFiniteMeasure ν] :
    ∃ c : ℝ, ν (Iio c) ≤ ν univ / 2 ∧ ν (Ioi c) ≤ ν univ / 2 := by
  set m := ν univ with hm
  have hmtop : m ≠ ⊤ := measure_ne_top ν univ
  rcases eq_or_ne m 0 with h0 | h0
  · refine ⟨0, ?_, ?_⟩ <;>
    · refine le_trans (measure_mono (subset_univ _)) ?_
      rw [← hm, h0]
      simp
  · have hhalf_lt : m / 2 < m := ENNReal.half_lt_self h0 hmtop
    have hhalf_pos : 0 < m / 2 := ENNReal.div_pos h0 (by norm_num)
    set S : Set ℝ := {t : ℝ | m / 2 ≤ ν (Iic t)} with hSdef
    have hne : S.Nonempty := by
      have h1 : Tendsto (fun x : ℝ => ν (Iic x)) atTop (𝓝 m) := tendsto_measure_Iic_atTop ν
      obtain ⟨t, ht⟩ := (h1.eventually (eventually_gt_nhds hhalf_lt)).exists
      exact ⟨t, ht.le⟩
    have hbot : Tendsto (fun x : ℝ => ν (Iic x)) atBot (𝓝 0) := by
      have hemp : (⋂ t : ℝ, Iic t) = ∅ := by
        ext x; simp; exact ⟨x - 1, by linarith⟩
      have h := tendsto_measure_iInter_atBot (μ := ν) (s := fun t : ℝ => Iic t)
        (fun t => measurableSet_Iic.nullMeasurableSet)
        (fun a b hab => Iic_subset_Iic.2 hab) ⟨0, measure_ne_top ν _⟩
      rw [hemp] at h
      simpa using h
    obtain ⟨b, hbb⟩ := (hbot.eventually (eventually_lt_nhds hhalf_pos)).exists
    have hbdd : BddBelow S := by
      refine ⟨b, fun t ht => ?_⟩
      by_contra hlt
      push_neg at hlt
      exact absurd (le_trans ht (measure_mono (Iic_subset_Iic.2 hlt.le))) (not_le.2 hbb)
    set c := sInf S with hc
    have hlt : ∀ t : ℝ, t < c → ν (Iic t) < m / 2 := by
      intro t htc
      by_contra h
      exact absurd (csInf_le hbdd (not_lt.1 h)) (not_le.2 htc)
    have hIio : ν (Iio c) ≤ m / 2 := by
      have hunion : (⋃ k : ℕ, Iic (c - 1 / ((k : ℝ) + 1))) = Iio c := by
        ext x
        simp only [mem_iUnion, mem_Iic, mem_Iio]
        constructor
        · rintro ⟨k, hk⟩
          have : (0:ℝ) < 1 / ((k : ℝ) + 1) := by positivity
          linarith
        · intro hx
          obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0:ℝ) < c - x by linarith)
          exact ⟨k, by linarith⟩
      have hmono : Monotone (fun k : ℕ => Iic (c - 1 / ((k : ℝ) + 1))) := by
        intro a b hab
        refine Iic_subset_Iic.2 ?_
        have hab' : ((a : ℝ) + 1) ≤ ((b : ℝ) + 1) := by
          have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
          linarith
        have := one_div_le_one_div_of_le (by positivity : (0:ℝ) < (a : ℝ) + 1) hab'
        linarith
      have htend := tendsto_measure_iUnion_atTop (μ := ν) hmono
      rw [hunion] at htend
      refine le_of_tendsto htend (Eventually.of_forall fun k => ?_)
      refine (hlt _ ?_).le
      have : (0:ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      simp only [Function.comp]
      linarith
    refine ⟨c, hIio, ?_⟩
    have hIic : m / 2 ≤ ν (Iic c) := by
      have hanti : Antitone (fun k : ℕ => Iic (c + 1 / ((k : ℝ) + 1))) := by
        intro a b hab
        refine Iic_subset_Iic.2 ?_
        have hab' : ((a : ℝ) + 1) ≤ ((b : ℝ) + 1) := by
          have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
          linarith
        have := one_div_le_one_div_of_le (by positivity : (0:ℝ) < (a : ℝ) + 1) hab'
        linarith
      have hinter : (⋂ k : ℕ, Iic (c + 1 / ((k : ℝ) + 1))) = Iic c := by
        ext x
        simp only [mem_iInter, mem_Iic]
        constructor
        · intro h
          by_contra hx
          push_neg at hx
          obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0:ℝ) < x - c by linarith)
          have := h k
          linarith
        · intro hx k
          have : (0:ℝ) < 1 / ((k : ℝ) + 1) := by positivity
          linarith
      have htend := tendsto_measure_iInter_atTop (μ := ν)
        (fun k : ℕ => measurableSet_Iic.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
      rw [hinter] at htend
      refine ge_of_tendsto htend (Eventually.of_forall fun k => ?_)
      obtain ⟨t, htS, htlt⟩ :=
        Real.lt_sInf_add_pos hne (show (0:ℝ) < 1 / ((k : ℝ) + 1) by positivity)
      simp only [Function.comp]
      exact le_trans htS (measure_mono (Iic_subset_Iic.2 htlt.le))
    have hcompl : ν (Iic c) + ν (Ioi c) = m := by
      have := measure_add_measure_compl (μ := ν) (measurableSet_Iic (a := c))
      rwa [compl_Iic] at this
    have h2 : m / 2 + ν (Ioi c) ≤ m / 2 + m / 2 := by
      calc m / 2 + ν (Ioi c) ≤ ν (Iic c) + ν (Ioi c) := by gcongr
        _ = m := hcompl
        _ = m / 2 + m / 2 := (ENNReal.add_halves m).symm
    exact (ENNReal.add_le_add_iff_left (by finiteness)).1 h2

/-! ## Hyperplanes -/

/-- The open half-space `{x | c < ⟪a, x⟫}` of `ℝ^n`. -/
def posHalf {n : ℕ} (a : Fin n → ℝ) (c : ℝ) : Set (Fin n → ℝ) :=
  {x | c < ∑ i, a i * x i}

/-- The open half-space `{x | ⟪a, x⟫ < c}` of `ℝ^n`. -/
def negHalf {n : ℕ} (a : Fin n → ℝ) (c : ℝ) : Set (Fin n → ℝ) :=
  {x | ∑ i, a i * x i < c}

/-- A single finite measure on `ℝ^n` (`n ≥ 1`) can be bisected by a hyperplane. -/
theorem exists_hyperplane_bisecting {n : ℕ} (hn : 0 < n) (μ : Measure (Fin n → ℝ))
    [IsFiniteMeasure μ] :
    ∃ (a : Fin n → ℝ) (c : ℝ), a ≠ 0 ∧
      μ (posHalf a c) ≤ μ univ / 2 ∧ μ (negHalf a c) ≤ μ univ / 2 := by
  obtain ⟨i0⟩ : Nonempty (Fin n) := Fin.pos_iff_nonempty.1 hn
  have hfm : Measurable (fun x : Fin n → ℝ => x i0) := measurable_pi_apply i0
  set ν := Measure.map (fun x : Fin n → ℝ => x i0) μ with hν
  have hνuniv : ν univ = μ univ := by
    rw [hν, Measure.map_apply hfm MeasurableSet.univ]
    simp
  haveI : IsFiniteMeasure ν := ⟨by rw [hνuniv]; exact measure_lt_top μ _⟩
  obtain ⟨c, h1, h2⟩ := exists_median ν
  have hsum : ∀ x : Fin n → ℝ, (∑ i, (Pi.single i0 (1:ℝ) : Fin n → ℝ) i * x i) = x i0 := by
    intro x
    simp [Pi.single_apply, ite_mul, Finset.sum_ite_eq']
  refine ⟨Pi.single i0 1, c, ?_, ?_, ?_⟩
  · intro h
    have h' := congrFun h i0
    simp at h'
  · have hset : posHalf (Pi.single i0 (1:ℝ)) c = (fun x : Fin n → ℝ => x i0) ⁻¹' (Ioi c) := by
      ext x
      simp [posHalf, hsum x, mem_Ioi]
    rw [hset, ← Measure.map_apply hfm measurableSet_Ioi, ← hν, ← hνuniv]
    exact h2
  · have hset : negHalf (Pi.single i0 (1:ℝ)) c = (fun x : Fin n → ℝ => x i0) ⁻¹' (Iio c) := by
      ext x
      simp [negHalf, hsum x, mem_Iio]
    rw [hset, ← Measure.map_apply hfm measurableSet_Iio, ← hν, ← hνuniv]
    exact h1

/-- **Ham Sandwich theorem, base case `n = 1`.**
Any family of `n = 1` finite measures on `ℝ^n = ℝ^1` can be simultaneously bisected by a
single hyperplane `{x | ⟪a, x⟫ = c}` with `a ≠ 0`: each open half-space carries at most half
of the total mass of each measure. -/
theorem ham_sandwich (μ : Fin 1 → Measure (Fin 1 → ℝ)) [∀ i, IsFiniteMeasure (μ i)] :
    ∃ (a : Fin 1 → ℝ) (c : ℝ), a ≠ 0 ∧
      ∀ i, μ i (posHalf a c) ≤ μ i univ / 2 ∧ μ i (negHalf a c) ≤ μ i univ / 2 := by
  obtain ⟨a, c, ha, hp, hm⟩ := exists_hyperplane_bisecting (n := 1) one_pos (μ 0)
  refine ⟨a, c, ha, fun i => ?_⟩
  have : i = 0 := Subsingleton.elim _ _
  subst this
  exact ⟨hp, hm⟩

end Frontier

