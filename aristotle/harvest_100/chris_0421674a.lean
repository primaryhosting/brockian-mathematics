/-
# Ham Sandwich
Category: Frontier Physics
Target: Frontier.ham_sandwich
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory Set Filter
open scoped ENNReal

namespace Frontier

/-- **Existence of a median.**  For a finite measure `μ` on a measurable space `α` and a
measurable real-valued function `f`, there is a real number `c` such that both the set where
`f` is strictly below `c` and the set where `f` is strictly above `c` have measure at most
half of the total mass. -/
theorem exists_median {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Measurable f) :
    ∃ c : ℝ, μ {x | f x < c} ≤ μ univ / 2 ∧ μ {x | c < f x} ≤ μ univ / 2 := by
  set m : ℝ≥0∞ := μ univ with hm
  have hmtop : m ≠ ∞ := measure_ne_top μ univ
  -- the sublevel sets
  set A : ℝ → Set α := fun t => {x | f x ≤ t} with hA
  have hAmeas : ∀ t, MeasurableSet (A t) := fun t => hf measurableSet_Iic
  have hAmono : Monotone A := by
    intro a b hab x hx
    exact le_trans hx hab
  rcases eq_or_ne m 0 with h0 | h0
  · refine ⟨0, ?_, ?_⟩ <;>
      exact le_trans (measure_mono (subset_univ _)) (by simp [← hm, h0])
  have hhalf_lt : m / 2 < m := ENNReal.half_lt_self h0 hmtop
  have hhalf_top : m / 2 ≠ ∞ := (hhalf_lt.trans_le le_top).ne
  -- the set of "upper medians"
  set S : Set ℝ := {t : ℝ | m / 2 ≤ μ (A t)} with hSdef
  have hSne : S.Nonempty := by
    have hunion : (⋃ n : ℕ, A (n : ℝ)) = univ := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true, hA, Set.mem_setOf_eq]
      obtain ⟨n, hn⟩ := exists_nat_ge (f x)
      exact ⟨n, hn⟩
    have hsup : m = ⨆ n : ℕ, μ (A (n : ℝ)) := by
      rw [hm, ← hunion]
      exact Monotone.measure_iUnion (fun a b hab => hAmono (by exact_mod_cast hab))
    have hlt : m / 2 < ⨆ n : ℕ, μ (A (n : ℝ)) := by rw [← hsup]; exact hhalf_lt
    obtain ⟨n, hn⟩ := lt_iSup_iff.1 hlt
    exact ⟨(n : ℝ), hn.le⟩
  have hSbdd : BddBelow S := by
    have hinter : (⋂ n : ℕ, A (-(n : ℝ))) = ∅ := by
      ext x
      simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, hA, Set.mem_setOf_eq,
        not_forall]
      obtain ⟨n, hn⟩ := exists_nat_gt (-(f x))
      exact ⟨n, by linarith⟩
    have hinf : (0 : ℝ≥0∞) = ⨅ n : ℕ, μ (A (-(n : ℝ))) := by
      rw [← measure_empty (μ := μ), ← hinter]
      refine Antitone.measure_iInter (fun a b hab => hAmono (by
        simp only [neg_le_neg_iff]
        exact_mod_cast hab)) (fun n => (hAmeas _).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩
    have hpos : (0 : ℝ≥0∞) < m / 2 := ENNReal.half_pos h0
    rw [hinf] at hpos
    obtain ⟨n, hn⟩ := iInf_lt_iff.1 hpos
    refine ⟨-(n : ℝ), fun s hs => ?_⟩
    by_contra hcon
    push_neg at hcon
    have : μ (A s) ≤ μ (A (-(n : ℝ))) := measure_mono (hAmono hcon.le)
    exact absurd (le_trans hs this) (not_le.2 hn)
  set c : ℝ := sInf S with hc
  have hlow : ∀ t : ℝ, t < c → μ (A t) < m / 2 := by
    intro t ht
    by_contra hcon
    push_neg at hcon
    exact absurd (csInf_le hSbdd (show t ∈ S from hcon)) (not_le.2 ht)
  have hhigh : ∀ t : ℝ, c < t → m / 2 ≤ μ (A t) := by
    intro t ht
    obtain ⟨s, hsS, hst⟩ := (csInf_lt_iff hSbdd hSne).1 ht
    exact le_trans hsS (measure_mono (hAmono hst.le))
  refine ⟨c, ?_, ?_⟩
  · have hset : {x | f x < c} = ⋃ n : ℕ, A (c - 1 / (n + 1)) := by
      ext x
      simp only [Set.mem_iUnion, hA, Set.mem_setOf_eq]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0:ℝ) < c - f x by linarith)
        exact ⟨n, by linarith⟩
      · rintro ⟨n, hn⟩
        have : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    rw [hset, Monotone.measure_iUnion]
    · refine iSup_le fun n => ?_
      refine (hlow _ ?_).le
      have : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · intro a b hab
      refine hAmono ?_
      have h1 : ((b : ℝ) + 1) > 0 := by positivity
      have h2 : ((a : ℝ) + 1) > 0 := by positivity
      have : (1:ℝ) / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) := by
        apply one_div_le_one_div_of_le h2
        have : (a : ℝ) ≤ b := by exact_mod_cast hab
        linarith
      linarith
  · have hset : A c = ⋂ n : ℕ, A (c + 1 / (n + 1)) := by
      ext x
      simp only [Set.mem_iInter, hA, Set.mem_setOf_eq]
      constructor
      · intro hx n
        have : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      · intro hx
        by_contra hcon
        push_neg at hcon
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0:ℝ) < f x - c by linarith)
        exact absurd (hx n) (not_le.2 (by linarith))
    have hAc : m / 2 ≤ μ (A c) := by
      rw [hset, Antitone.measure_iInter]
      · refine le_iInf fun n => hhigh _ ?_
        have : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      · intro a b hab
        refine hAmono ?_
        have h2 : ((a : ℝ) + 1) > 0 := by positivity
        have : (1:ℝ) / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) := by
          apply one_div_le_one_div_of_le h2
          have : (a : ℝ) ≤ b := by exact_mod_cast hab
          linarith
        linarith
      · exact fun n => (hAmeas _).nullMeasurableSet
      · exact ⟨0, measure_ne_top _ _⟩
    have hcompl : {x | c < f x} = (A c)ᶜ := by
      ext x
      simp [hA, not_le]
    have hsum : μ {x | c < f x} + μ (A c) = m := by
      rw [hcompl, hm, ← measure_union (disjoint_compl_left) (hAmeas c)]
      congr 1
      simp
    have : μ {x | c < f x} + m / 2 ≤ m / 2 + m / 2 := by
      calc μ {x | c < f x} + m / 2 ≤ μ {x | c < f x} + μ (A c) := by
            gcongr
        _ = m := hsum
        _ = m / 2 + m / 2 := (ENNReal.add_halves m).symm
    exact ENNReal.add_le_add_iff_right hhalf_top |>.1 this

/-- **Ham–Sandwich, base case `n = 1`.**  Any family of `1` finite (Borel) measures on the
Euclidean space `ℝ¹` can be simultaneously bisected by a hyperplane `{x | ⟪v, x⟫ = c}` with
`v ≠ 0`: each open half-space determined by the hyperplane carries at most half of the
corresponding total mass. -/
theorem ham_sandwich (μ : Fin 1 → Measure (EuclideanSpace ℝ (Fin 1)))
    [∀ i, IsFiniteMeasure (μ i)] :
    ∃ (v : EuclideanSpace ℝ (Fin 1)) (c : ℝ), v ≠ 0 ∧
      ∀ i, μ i {x | inner ℝ v x < c} ≤ μ i univ / 2 ∧
           μ i {x | c < inner ℝ v x} ≤ μ i univ / 2 := by
  classical
  set v : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1 with hv
  have hvx : ∀ x : EuclideanSpace ℝ (Fin 1), inner ℝ v x = x 0 := by
    intro x
    rw [hv, EuclideanSpace.inner_single_left]
    simp
  have hfmeas : Measurable (fun x : EuclideanSpace ℝ (Fin 1) => x 0) := by
    have : Continuous (fun x : EuclideanSpace ℝ (Fin 1) => x 0) :=
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).continuous
    exact this.measurable
  obtain ⟨c, h1, h2⟩ := exists_median (μ 0) hfmeas
  refine ⟨v, c, ?_, ?_⟩
  · intro hcon
    have := congrFun (congrArg (fun y : EuclideanSpace ℝ (Fin 1) => (y : Fin 1 → ℝ)) hcon) 0
    simp [hv] at this
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    constructor
    · simpa only [hvx] using h1
    · simpa only [hvx] using h2

end Frontier

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

