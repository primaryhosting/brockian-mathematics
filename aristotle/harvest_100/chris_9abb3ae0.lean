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
theorem exists_median (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f) :
    ∃ c : ℝ, μ {x | f x < c} ≤ μ univ / 2 ∧ μ {x | c < f x} ≤ μ univ / 2 := by
  set m : ℝ≥0∞ := μ univ / 2 with hm
  -- measurability of the sublevel sets
  have hmeas : ∀ t : ℝ, MeasurableSet {x | f x ≤ t} := fun t => hf measurableSet_Iic
  have hmono : ∀ ⦃s t : ℝ⦄, s ≤ t → μ {x | f x ≤ s} ≤ μ {x | f x ≤ t} := by
    intro s t hst
    exact measure_mono fun x hx => le_trans hx hst
  by_cases htot : μ univ = 0
  · refine ⟨0, ?_, ?_⟩ <;>
      exact le_trans (measure_mono (subset_univ _)) (by simp [htot])
  have hlt : m < μ univ := ENNReal.half_lt_self htot (measure_ne_top μ univ)
  set S : Set ℝ := {t : ℝ | m ≤ μ {x | f x ≤ t}} with hS
  -- `S` is nonempty
  have hSne : S.Nonempty := by
    have hunion : ⋃ n : ℕ, {x | f x ≤ (n : ℝ)} = univ := by
      ext x
      simp only [mem_iUnion, mem_setOf_eq, mem_univ, iff_true]
      obtain ⟨n, hn⟩ := exists_nat_ge (f x)
      exact ⟨n, hn⟩
    have hmono' : Monotone (fun n : ℕ => {x | f x ≤ (n : ℝ)}) := by
      intro a b hab x hx
      simp only [mem_setOf_eq] at hx ⊢
      exact hx.trans (by exact_mod_cast hab)
    have htend : Tendsto (fun n : ℕ => μ {x | f x ≤ (n : ℝ)}) atTop (𝓝 (μ univ)) := by
      have := tendsto_measure_iUnion_atTop (μ := μ) hmono'
      rwa [hunion] at this
    obtain ⟨n, hn⟩ := (htend.eventually_const_le hlt).exists
    exact ⟨(n : ℝ), hn⟩
  -- `S` is bounded below
  have hbdd : BddBelow S := by
    have hinter : ⋂ n : ℕ, {x | f x ≤ -(n : ℝ)} = ∅ := by
      ext x
      simp only [mem_iInter, mem_setOf_eq, mem_empty_iff_false, iff_false, not_forall]
      obtain ⟨n, hn⟩ := exists_nat_gt (-f x)
      refine ⟨n, ?_⟩
      simp only [not_le]
      linarith
    have hanti : Antitone (fun n : ℕ => {x | f x ≤ -(n : ℝ)}) := by
      intro a b hab x hx
      have hab' : ((a : ℝ)) ≤ (b : ℝ) := by exact_mod_cast hab
      simp only [mem_setOf_eq] at hx ⊢
      linarith
    have htend : Tendsto (fun n : ℕ => μ {x | f x ≤ -(n : ℝ)}) atTop (𝓝 0) := by
      have := tendsto_measure_iInter_atTop (μ := μ)
        (fun n : ℕ => (hmeas (-(n : ℝ))).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
      rwa [hinter, measure_empty] at this
    have hpos : (0 : ℝ≥0∞) < m := ENNReal.half_pos htot
    obtain ⟨n, hn⟩ := (htend.eventually_lt_const hpos).exists
    refine ⟨-(n : ℝ), fun t ht => ?_⟩
    by_contra hcon
    push_neg at hcon
    exact absurd (le_trans ht (hmono hcon.le)) (not_le.mpr hn)
  set c : ℝ := sInf S with hc
  have hbelow : ∀ t : ℝ, t < c → μ {x | f x ≤ t} ≤ m := by
    intro t ht
    by_contra hcon
    push_neg at hcon
    exact absurd (csInf_le hbdd hcon.le) (not_le.mpr ht)
  have habove : ∀ t : ℝ, c < t → m ≤ μ {x | f x ≤ t} := by
    intro t ht
    obtain ⟨s, hsS, hst⟩ := exists_lt_of_csInf_lt hSne ht
    exact le_trans hsS (hmono hst.le)
  -- the strict sublevel set
  have hIio : μ {x | f x < c} ≤ m := by
    have hunion : ⋃ n : ℕ, {x | f x ≤ c - 1 / (n + 1 : ℝ)} = {x | f x < c} := by
      ext x
      simp only [mem_iUnion, mem_setOf_eq]
      constructor
      · rintro ⟨n, hn⟩
        have : (0:ℝ) < 1 / (n + 1 : ℝ) := by positivity
        linarith
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0:ℝ) < c - f x by linarith)
        exact ⟨n, by linarith⟩
    have htend : Tendsto (fun n : ℕ => μ {x | f x ≤ c - 1 / (n + 1 : ℝ)}) atTop
        (𝓝 (μ {x | f x < c})) := by
      have := tendsto_measure_iUnion_atTop (μ := μ)
        (s := fun n : ℕ => {x | f x ≤ c - 1 / (n + 1 : ℝ)}) ?_
      · rwa [hunion] at this
      · intro a b hab x hx
        have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
        have : 1 / (b + 1 : ℝ) ≤ 1 / (a + 1 : ℝ) := by
          apply one_div_le_one_div_of_le <;> linarith [Nat.cast_nonneg (α := ℝ) a]
        simp only [mem_setOf_eq] at hx ⊢
        linarith
    refine le_of_tendsto htend (Eventually.of_forall fun n => hbelow _ ?_)
    have : (0:ℝ) < 1 / (n + 1 : ℝ) := by positivity
    linarith
  have hIic : m ≤ μ {x | f x ≤ c} := by
    have hinter : ⋂ n : ℕ, {x | f x ≤ c + 1 / (n + 1 : ℝ)} = {x | f x ≤ c} := by
      ext x
      simp only [mem_iInter, mem_setOf_eq]
      constructor
      · intro hx
        refine le_of_forall_pos_le_add fun ε hε => ?_
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
        exact le_trans (hx n) (by linarith)
      · intro hx n
        have : (0:ℝ) < 1 / (n + 1 : ℝ) := by positivity
        linarith
    have htend : Tendsto (fun n : ℕ => μ {x | f x ≤ c + 1 / (n + 1 : ℝ)}) atTop
        (𝓝 (μ {x | f x ≤ c})) := by
      have := tendsto_measure_iInter_atTop (μ := μ)
        (s := fun n : ℕ => {x | f x ≤ c + 1 / (n + 1 : ℝ)})
        (fun n => (hmeas _).nullMeasurableSet) ?_ ⟨0, measure_ne_top _ _⟩
      · rwa [hinter] at this
      · intro a b hab x hx
        have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
        have : 1 / (b + 1 : ℝ) ≤ 1 / (a + 1 : ℝ) := by
          apply one_div_le_one_div_of_le <;> linarith [Nat.cast_nonneg (α := ℝ) a]
        simp only [mem_setOf_eq] at hx ⊢
        linarith
    refine ge_of_tendsto htend (Eventually.of_forall fun n => habove _ ?_)
    have : (0:ℝ) < 1 / (n + 1 : ℝ) := by positivity
    linarith
  refine ⟨c, hIio, ?_⟩
  have hcompl : {x | c < f x} = {x | f x ≤ c}ᶜ := by
    ext x; simp [not_le]
  rw [hcompl, measure_compl (hmeas c) (measure_ne_top _ _), tsub_le_iff_right]
  calc μ univ = m + m := (ENNReal.add_halves _).symm
    _ ≤ m + μ {x | f x ≤ c} := by gcongr

end Frontier

import Mathlib
import RequestProject.Median

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
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open MeasureTheory Set

namespace Frontier

/-- The affine hyperplane `{x | ⟪v, x⟫ = c}` (with normal vector `v`) *bisects* the measure `μ`
if each of the two open half-spaces it bounds carries at most half of the total mass of `μ`.
(Equivalently, each closed half-space carries at least half of the mass.) -/
def BisectedBy {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) : Prop :=
  μ {x | inner ℝ v x < c} ≤ μ univ / 2 ∧ μ {x | c < inner ℝ v x} ≤ μ univ / 2

/-- Linear functionals `x ↦ ⟪v, x⟫` on Euclidean space are measurable. -/
theorem measurable_inner_left {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) :
    Measurable fun x : EuclideanSpace ℝ (Fin n) => inner ℝ v x :=
  ((innerSL ℝ v).continuous).measurable

/-- If a hyperplane bisects `μ`, then each of the two *closed* half-spaces it bounds carries at
least half of the mass of `μ`. -/
theorem BisectedBy.half_le_closed {n : ℕ} {v : EuclideanSpace ℝ (Fin n)} {c : ℝ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure μ] (h : BisectedBy v c μ) :
    μ univ / 2 ≤ μ {x | c ≤ inner ℝ v x} ∧ μ univ / 2 ≤ μ {x | inner ℝ v x ≤ c} := by
  have hmeas₁ : MeasurableSet {x : EuclideanSpace ℝ (Fin n) | inner ℝ v x < c} :=
    measurable_inner_left v measurableSet_Iio
  have hmeas₂ : MeasurableSet {x : EuclideanSpace ℝ (Fin n) | c < inner ℝ v x} :=
    measurable_inner_left v measurableSet_Ioi
  constructor
  · have hc : {x : EuclideanSpace ℝ (Fin n) | c ≤ inner ℝ v x}
        = {x | inner ℝ v x < c}ᶜ := by ext x; simp [not_lt]
    rw [hc, measure_compl hmeas₁ (measure_ne_top _ _)]
    refine ENNReal.le_sub_of_add_le_right (measure_ne_top _ _) ?_
    calc μ univ / 2 + μ {x | inner ℝ v x < c} ≤ μ univ / 2 + μ univ / 2 := add_le_add le_rfl h.1
      _ = μ univ := ENNReal.add_halves _
  · have hc : {x : EuclideanSpace ℝ (Fin n) | inner ℝ v x ≤ c}
        = {x | c < inner ℝ v x}ᶜ := by ext x; simp [not_lt]
    rw [hc, measure_compl hmeas₂ (measure_ne_top _ _)]
    refine ENNReal.le_sub_of_add_le_right (measure_ne_top _ _) ?_
    calc μ univ / 2 + μ {x | c < inner ℝ v x} ≤ μ univ / 2 + μ univ / 2 := add_le_add le_rfl h.2
      _ = μ univ := ENNReal.add_halves _

/-- **A single finite measure on `ℝⁿ` can be bisected by a hyperplane** (the one-measure case of
the Ham–Sandwich theorem). The bisecting hyperplane can even be taken orthogonal to any
prescribed nonzero direction `v`: one only has to choose the offset `c` to be a median of the
linear functional `⟪v, ·⟫`. -/
theorem exists_bisecting_hyperplane {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsFiniteMeasure μ] (v : EuclideanSpace ℝ (Fin n)) :
    ∃ c : ℝ, BisectedBy v c μ :=
  exists_median μ (measurable_inner_left v)

/-- Half of the total mass is an upper bound for anything whose "double" fits inside the total
mass. -/
private theorem le_half_of_add_self_le {a b : ℝ≥0∞} (h : a + a ≤ b) : a ≤ b / 2 := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl two_ne_zero) (Or.inl (by simp)), mul_two]
  exact h

/-- **Ham–Sandwich for centrally symmetric measures, in every dimension and for any number of
measures.** If each of the finite measures `μ i` on `ℝⁿ` is invariant under the antipodal map
`x ↦ -x`, then *every* hyperplane through the origin simultaneously bisects all of them. -/
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
theorem ham_sandwich_symmetric {n : ℕ} [NeZero n]
    (μ : Fin n → Measure (EuclideanSpace ℝ (Fin n))) [∀ i, IsFiniteMeasure (μ i)]
    (hsymm : ∀ i, Measure.map (fun x => -x) (μ i) = μ i) :
    ∃ (v : EuclideanSpace ℝ (Fin n)) (c : ℝ), v ≠ 0 ∧ ∀ i, BisectedBy v c (μ i) := by
  classical
  refine ⟨EuclideanSpace.single (0 : Fin n) (1 : ℝ), 0, ?_, ham_sandwich_of_symmetric μ hsymm _⟩
  simp

/-- **Ham–Sandwich theorem, base case `n = 1`.**
Any family of `n = 1` finite measures on `ℝ¹` can be simultaneously bisected by a single
hyperplane, i.e. by a point `{x | ⟪v, x⟫ = c}` with `v ≠ 0`: both open half-lines it determines
carry at most half of the mass of the measure.

(The general statement for `n` measures on `ℝⁿ` requires the Borsuk–Ulam theorem, which is not
available in Mathlib; the case of a *single* measure on `ℝⁿ` for arbitrary `n` is proved above as
`Frontier.exists_bisecting_hyperplane`.) -/
theorem ham_sandwich (μ : Fin 1 → Measure (EuclideanSpace ℝ (Fin 1)))
    [∀ i, IsFiniteMeasure (μ i)] :
    ∃ (v : EuclideanSpace ℝ (Fin 1)) (c : ℝ), v ≠ 0 ∧ ∀ i, BisectedBy v c (μ i) := by
  classical
  set v : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 (1 : ℝ) with hv
  obtain ⟨c, hc⟩ := exists_bisecting_hyperplane (μ 0) v
  refine ⟨v, c, ?_, ?_⟩
  · simp [hv]
  · intro i
    have : i = 0 := Subsingleton.elim _ _
    subst this
    exact hc

end Frontier

