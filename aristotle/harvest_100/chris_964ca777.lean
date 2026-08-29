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

import Mathlib

/-!
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open Filter Topology

set_option maxHeartbeats 1000000

namespace Brockian.Equidistribution

/-- `countBelow x N a` is the number of indices `n < N` whose fractional part
`Int.fract (x n)` is smaller than `a`. -/
noncomputable def countBelow (x : ℕ → ℝ) (N : ℕ) (a : ℝ) : ℕ :=
  ((Finset.range N).filter (fun n => Int.fract (x n) < a)).card

/-- The empirical proportion of the first `N` terms of `x` whose fractional part lies
below `a`. -/
noncomputable def prop (x : ℕ → ℝ) (N : ℕ) (a : ℝ) : ℝ :=
  (countBelow x N a : ℝ) / N

lemma countBelow_mono (x : ℕ → ℝ) (N : ℕ) {a b : ℝ} (hab : a ≤ b) :
    countBelow x N a ≤ countBelow x N b := by
  refine Finset.card_le_card ?_
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨hn.1, lt_of_lt_of_le hn.2 hab⟩

lemma countBelow_le (x : ℕ → ℝ) (N : ℕ) (a : ℝ) : countBelow x N a ≤ N := by
  simpa using Finset.card_filter_le (Finset.range N) (fun n => Int.fract (x n) < a)

lemma prop_nonneg (x : ℕ → ℝ) (N : ℕ) (a : ℝ) : 0 ≤ prop x N a :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma prop_le_one (x : ℕ → ℝ) (N : ℕ) (a : ℝ) : prop x N a ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [prop, hN]
  · rw [prop, div_le_one (by exact_mod_cast hN)]
    exact_mod_cast countBelow_le x N a

lemma prop_mono (x : ℕ → ℝ) (N : ℕ) {a b : ℝ} (hab : a ≤ b) :
    prop x N a ≤ prop x N b := by
  refine div_le_div_of_nonneg_right ?_ ?_ |>.trans_eq rfl
  · exact_mod_cast countBelow_mono x N hab
  · exact Nat.cast_nonneg _

/-- **Equidistribution from asymptotics on a dense set of thresholds.**

Let `x : ℕ → ℝ` be a sequence and let `D` be a set of thresholds that is dense in the
unit interval (between any two points of `[0,1]` there is a point of `D`).  Assume that
for every threshold `a ∈ D` the asymptotic proportion of terms with fractional part below
`a` exists and equals `a`.  Then the sequence is equidistributed modulo one: for *every*
`a ∈ [0,1]` the asymptotic proportion exists and equals `a`. -/
theorem equidistribution_of_asymptotic_exists
    (x : ℕ → ℝ) (D : Set ℝ)
    (hD : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ 1 → ∃ d ∈ D, u < d ∧ d < v)
    (hlim : ∀ a ∈ D, Tendsto (fun N => prop x N a) atTop (𝓝 a))
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Tendsto (fun N => prop x N a) atTop (𝓝 a) := by
  rw [tendsto_order]
  constructor
  · intro b hb
    rcases lt_or_ge b 0 with hb0 | hb0
    · exact Eventually.of_forall fun N => lt_of_lt_of_le hb0 (prop_nonneg x N a)
    · obtain ⟨d, hdD, hbd, hda⟩ := hD b a hb0 hb ha1
      filter_upwards [(tendsto_order.1 (hlim d hdD)).1 b hbd] with N hN
      exact hN.trans_le (prop_mono x N hda.le)
  · intro b hb
    rcases le_or_gt b 1 with hb1 | hb1
    · obtain ⟨d, hdD, had, hdb⟩ := hD a b ha0 hb hb1
      filter_upwards [(tendsto_order.1 (hlim d hdD)).2 b hdb] with N hN
      exact lt_of_le_of_lt (prop_mono x N had.le) hN
    · exact Eventually.of_forall fun N => lt_of_le_of_lt (prop_le_one x N a) hb1

/-- `countIn x N a b` is the number of indices `n < N` whose fractional part lies in the
interval `[a, b)`. -/
noncomputable def countIn (x : ℕ → ℝ) (N : ℕ) (a b : ℝ) : ℕ :=
  ((Finset.range N).filter (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)).card

lemma countBelow_add_countIn (x : ℕ → ℝ) (N : ℕ) {a b : ℝ} (hab : a ≤ b) :
    countBelow x N a + countIn x N a b = countBelow x N b := by
  classical
  have hsplit :
      (Finset.range N).filter (fun n => Int.fract (x n) < b) =
        ((Finset.range N).filter (fun n => Int.fract (x n) < a)) ∪
          ((Finset.range N).filter (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)) := by
    ext n
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hn, hlt⟩
      rcases lt_or_ge (Int.fract (x n)) a with h | h
      · exact Or.inl ⟨hn, h⟩
      · exact Or.inr ⟨hn, h, hlt⟩
    · rintro (⟨hn, h⟩ | ⟨hn, h1, h2⟩)
      · exact ⟨hn, lt_of_lt_of_le h hab⟩
      · exact ⟨hn, h2⟩
  have hdisj :
      Disjoint ((Finset.range N).filter (fun n => Int.fract (x n) < a))
        ((Finset.range N).filter (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)) := by
    refine Finset.disjoint_left.2 ?_
    intro n hn hn'
    simp only [Finset.mem_filter] at hn hn'
    exact absurd hn'.2.1 (not_le.2 hn.2)
  rw [countBelow, countBelow, countIn, hsplit, Finset.card_union_of_disjoint hdisj]

/-- **Equidistribution on subintervals.**  Under the hypotheses of
`equidistribution_of_asymptotic_exists`, the proportion of the first `N` terms whose
fractional part lies in `[a, b) ⊆ [0, 1]` tends to the length `b - a`. -/
theorem equidistribution_Ico_of_asymptotic_exists
    (x : ℕ → ℝ) (D : Set ℝ)
    (hD : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ 1 → ∃ d ∈ D, u < d ∧ d < v)
    (hlim : ∀ a ∈ D, Tendsto (fun N => prop x N a) atTop (𝓝 a))
    {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    Tendsto (fun N => (countIn x N a b : ℝ) / N) atTop (𝓝 (b - a)) := by
  have key : ∀ N : ℕ, (countIn x N a b : ℝ) / N = prop x N b - prop x N a := by
    intro N
    have h := congrArg (fun m : ℕ => (m : ℝ)) (countBelow_add_countIn x N hab)
    push_cast at h
    rw [prop, prop, div_sub_div_same]
    congr 1
    linarith
  simp only [key]
  exact (equidistribution_of_asymptotic_exists x D hD hlim (ha0.trans hab) hb1).sub
    (equidistribution_of_asymptotic_exists x D hD hlim ha0 (hab.trans hb1))

end Brockian.Equidistribution

