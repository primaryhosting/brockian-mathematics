import Mathlib

/-!
# Medians of real-valued measurable functions

Auxiliary file for the Ham Sandwich development: every finite measure has a median
along any measurable real-valued function.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Frontier

variable {α : Type*} [MeasurableSpace α]

/-- **Existence of a median.** For a finite measure `μ` on `α` and a measurable function
`f : α → ℝ` there is a threshold `c` such that both `{f < c}` and `{f > c}` carry at most
half of the total mass. -/

theorem ham_sandwich_of_symmetric {n : ℕ} {ι : Type*} (μ : ι → Measure (EuclideanSpace ℝ (Fin n)))
    [∀ i, IsFiniteMeasure (μ i)] (hsymm : ∀ i, Measure.map (fun x => -x) (μ i) = μ i)
    (v : EuclideanSpace ℝ (Fin n)) : ∀ i, BisectedBy v 0 (μ i) := by
  have key : ∀ (ν : Measure (EuclideanSpace ℝ (Fin n))), IsFiniteMeasure ν →
      Measure.map (fun x => -x) ν = ν → ν {x | inner ℝ v x < 0} ≤ ν univ / 2 := by
    intro ν _ hs
    set A := {x : EuclideanSpace ℝ (Fin n) | inner ℝ v x < 0} with hA
    set B := {x : EuclideanSpace ℝ (Fin n) | 0 < inner ℝ v x} with hB
    have hAm : MeasurableSet A := measurable_inner_left v measurableSet_Iio
    have hBm : MeasurableSet B := measurable_inner_left v measurableSet_Ioi
    have hpre : (fun x : EuclideanSpace ℝ (Fin n) => -x) ⁻¹' A = B := by
      ext x; simp [hA, hB, inner_neg_right]
    have hBA : ν B = ν A := by
      rw [← hpre, ← Measure.map_apply measurable_neg hAm, hs]
    have hdisj : Disjoint A B := by
      rw [Set.disjoint_left]
      intro x hx hx'
      simp only [hA, hB, mem_setOf_eq] at hx hx'
      linarith
    have hsum : ν A + ν A ≤ ν univ := by
      have h2 : ν A + ν A = ν (A ∪ B) := by rw [measure_union hdisj hBm, hBA]
      rw [h2]
      exact measure_mono (subset_univ _)
    exact le_half_of_add_self_le hsum
  intro i
  have h' := key (μ i) inferInstance (hsymm i)
  refine ⟨h', ?_⟩
  -- the opposite open half-space is the image of the first one under the antipodal map
  have hset : {x : EuclideanSpace ℝ (Fin n) | (0 : ℝ) < inner ℝ v x}
      = (fun x : EuclideanSpace ℝ (Fin n) => -x) ⁻¹' {x | inner ℝ v x < 0} := by
    ext x; simp [inner_neg_right]
  have hmeasA : MeasurableSet {x : EuclideanSpace ℝ (Fin n) | inner ℝ v x < 0} :=
    measurable_inner_left v measurableSet_Iio
  rw [hset, ← Measure.map_apply measurable_neg hmeasA, hsymm i]
  exact h'

/-- **Ham–Sandwich for `n` centrally symmetric finite measures on `ℝⁿ`.**
If each of `n ≥ 1` finite measures on `ℝⁿ` is invariant under `x ↦ -x`, then a single hyperplane
(any hyperplane through the origin) simultaneously bisects all of them. -/
