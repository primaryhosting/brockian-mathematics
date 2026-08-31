/-!
# Config Count Density Of BV
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_density_of_BV
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
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


/-!
# Equidistribution and the bounded-variation reduction for configuration counts

Let `u : ℕ → ℝ` be a sequence which is *equidistributed* in the unit interval, in the sense
that averages of continuous test functions along `u` converge to the corresponding integral
over `[0,1]` (`Brockian.EquidistributionBVReduction.Equidistributed`).

The main result, `Brockian.EquidistributionBVReduction.configCount_density_of_BV`, upgrades
this from continuous test functions to the indicator of an interval `[a, b) ⊆ [0,1]`, which is
the basic function of bounded variation: the number of indices `n < N` with `u n ∈ [a, b)`
has density `b - a`.

The proof is the usual sandwich argument: the indicator of `[a, b)` is squeezed between two
continuous functions (produced by Urysohn's lemma) whose integrals differ from `b - a` by an
arbitrarily small amount.
-/

open MeasureTheory Set Filter Topology

namespace Brockian
namespace EquidistributionBVReduction

open Classical in
/-- `configCount u S N` is the number of indices `n < N` for which `u n` lies in `S`. -/
noncomputable def configCount (u : ℕ → ℝ) (S : Set ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => u n ∈ S)).card

/-- The configuration count, as a real number, is the sum of the indicator of the target set
along the sequence. -/
lemma configCount_eq_sum_indicator (u : ℕ → ℝ) (S : Set ℝ) (N : ℕ) :
    (configCount u S N : ℝ) = ∑ n ∈ Finset.range N, S.indicator (fun _ => (1 : ℝ)) (u n) := by
  classical
  rw [configCount, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl ?_
  intro n _
  by_cases h : u n ∈ S <;> simp [h]

/-- A sequence is equidistributed in `[0,1]` if the averages of every continuous test function
along the sequence converge to its integral over `[0,1]`. -/
def Equidistributed (u : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Continuous f →
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (u n)) / N) atTop (𝓝 (∫ x in (0 : ℝ)..1, f x))

/-- A configuration count is bounded above by the sum of any nonnegative test function which
dominates the indicator of the target set. -/
lemma configCount_le_sum (u : ℕ → ℝ) (S : Set ℝ) (N : ℕ) (f : ℝ → ℝ)
    (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x ∈ S, (1 : ℝ) ≤ f x) :
    (configCount u S N : ℝ) ≤ ∑ n ∈ Finset.range N, f (u n) := by
  rw [configCount_eq_sum_indicator]
  refine Finset.sum_le_sum fun n _ => ?_
  by_cases hn : u n ∈ S
  · simpa [Set.indicator_of_mem hn] using h1 _ hn
  · simpa [Set.indicator_of_notMem hn] using h0 (u n)

/-- The sum of a test function bounded by `1` and supported in the target set is bounded above
by the configuration count. -/
lemma sum_le_configCount (u : ℕ → ℝ) (S : Set ℝ) (N : ℕ) (g : ℝ → ℝ)
    (h1 : ∀ x, g x ≤ 1) (hsupp : ∀ x ∉ S, g x = 0) :
    ∑ n ∈ Finset.range N, g (u n) ≤ (configCount u S N : ℝ) := by
  rw [configCount_eq_sum_indicator]
  refine Finset.sum_le_sum fun n _ => ?_
  by_cases hn : u n ∈ S
  · simpa [Set.indicator_of_mem hn] using h1 (u n)
  · simp [Set.indicator_of_notMem hn, hsupp _ hn]

/-- A nonnegative continuous function bounded by `1` and supported in `(p, q)` has integral over
`[0,1]` at most `q - p`. -/
lemma integral_le_of_support_subset (f : ℝ → ℝ) (hf : Continuous f) (h0 : ∀ x, 0 ≤ f x)
    (h1 : ∀ x, f x ≤ 1) {p q : ℝ} (hpq : p ≤ q) (hsupp : ∀ x ∉ Ioo p q, f x = 0) :
    (∫ x in (0 : ℝ)..1, f x) ≤ q - p := by
  have hint : Integrable f volume := by
    refine hf.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (isCompact_Icc (a := p) (b := q)) ?_
    intro x hx
    exact hsupp x fun hx' => hx (Ioo_subset_Icc_self hx')
  have hbound : (∫ x in Ioo p q, f x) ≤ ∫ _x in Ioo p q, (1 : ℝ) :=
    setIntegral_mono_on hint.integrableOn
      (integrableOn_const (by simp [Real.volume_Ioo])) measurableSet_Ioo fun x _ => h1 x
  have hconst : (∫ _x in Ioo p q, (1 : ℝ)) = q - p := by
    rw [setIntegral_const]
    simp [Real.volume_real_Ioo, max_eq_left (sub_nonneg.mpr hpq)]
  calc (∫ x in (0 : ℝ)..1, f x) = ∫ x in Ioc (0 : ℝ) 1, f x :=
        intervalIntegral.integral_of_le zero_le_one
    _ ≤ ∫ x, f x := setIntegral_le_integral hint (Filter.Eventually.of_forall h0)
    _ = ∫ x in Ioo p q, f x := (setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm
    _ ≤ ∫ _x in Ioo p q, (1 : ℝ) := hbound
    _ = q - p := hconst

/-- A nonnegative continuous function which is at least `1` on `[c, d] ⊆ (0,1]` has integral
over `[0,1]` at least `d - c`. -/
lemma le_integral_of_one_le_on (g : ℝ → ℝ) (hg : Continuous g) (h0 : ∀ x, 0 ≤ g x)
    {c d : ℝ} (hcd : c ≤ d) (hc : 0 < c) (hd : d ≤ 1) (h1 : ∀ x ∈ Icc c d, (1 : ℝ) ≤ g x) :
    d - c ≤ ∫ x in (0 : ℝ)..1, g x := by
  have hsub : Icc c d ⊆ Ioc (0 : ℝ) 1 := fun x hx => ⟨lt_of_lt_of_le hc hx.1, hx.2.trans hd⟩
  have hconst : (∫ _x in Icc c d, (1 : ℝ)) = d - c := by
    rw [setIntegral_const]
    simp [Real.volume_real_Icc, max_eq_left (sub_nonneg.mpr hcd)]
  have hstep1 : (∫ _x in Icc c d, (1 : ℝ)) ≤ ∫ x in Icc c d, g x :=
    setIntegral_mono_on (integrableOn_const (by simp [Real.volume_Icc]))
      hg.integrableOn_Icc measurableSet_Icc fun x hx => h1 x hx
  have hstep2 : (∫ x in Icc c d, g x) ≤ ∫ x in Ioc (0 : ℝ) 1, g x :=
    setIntegral_mono_set hg.integrableOn_Ioc (Filter.Eventually.of_forall h0)
      (HasSubset.Subset.eventuallyLE hsub)
  rw [intervalIntegral.integral_of_le zero_le_one, ← hconst]
  exact hstep1.trans hstep2

/-- Eventually, the configuration density for `[a, b)` is bounded above by `b - a + 3δ`. -/
lemma eventually_configCount_div_le (u : ℕ → ℝ) (hequi : Equidistributed u) {a b : ℝ}
    (hab : a ≤ b) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, (configCount u (Ico a b) N : ℝ) / N ≤ (b - a) + 3 * δ := by
  obtain ⟨f, hf1, hf0, -, hfmem⟩ :=
    exists_continuous_one_zero_of_isCompact (X := ℝ) (s := Icc a b)
      (t := (Ioo (a - δ) (b + δ))ᶜ) isCompact_Icc isOpen_Ioo.isClosed_compl
      (Set.disjoint_compl_right_iff_subset.mpr
        (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩))
  have hInt : (∫ x in (0 : ℝ)..1, f x) ≤ (b - a) + 2 * δ := by
    have := integral_le_of_support_subset (f := fun x => f x) f.continuous
      (fun x => (hfmem x).1) (fun x => (hfmem x).2) (p := a - δ) (q := b + δ)
      (by linarith) (fun x hx => hf0 hx)
    linarith [this]
  have hev : ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Finset.range N, f (u n)) / N < (∫ x in (0 : ℝ)..1, f x) + δ :=
    Filter.Tendsto.eventually_lt_const (by linarith) (hequi (fun x => f x) f.continuous)
  filter_upwards [hev, eventually_gt_atTop 0] with N hN hN0
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hcount : (configCount u (Ico a b) N : ℝ) ≤ ∑ n ∈ Finset.range N, f (u n) :=
    configCount_le_sum u _ N _ (fun x => (hfmem x).1)
      (fun x hx => by
        have h := hf1 (Ico_subset_Icc_self hx)
        simp only [Pi.one_apply] at h
        simp [h])
  have : (configCount u (Ico a b) N : ℝ) / N ≤ (∑ n ∈ Finset.range N, f (u n)) / N := by
    gcongr
  linarith [hN, this]

/-- Eventually, the configuration density for `[a, b)` is bounded below by `b - a - 3δ`. -/
lemma eventually_le_configCount_div (u : ℕ → ℝ) (hequi : Equidistributed u) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, (b - a) - 3 * δ ≤ (configCount u (Ico a b) N : ℝ) / N := by
  by_cases hsmall : b - a ≤ 2 * δ
  · filter_upwards with N
    have h0 : (0 : ℝ) ≤ (configCount u (Ico a b) N : ℝ) / N := by positivity
    linarith
  push_neg at hsmall
  obtain ⟨g, hg1, hg0, -, hgmem⟩ :=
    exists_continuous_one_zero_of_isCompact (X := ℝ) (s := Icc (a + δ) (b - δ))
      (t := (Ioo a b)ᶜ) isCompact_Icc isOpen_Ioo.isClosed_compl
      (Set.disjoint_compl_right_iff_subset.mpr
        (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩))
  have hInt : (b - a) - 2 * δ ≤ ∫ x in (0 : ℝ)..1, g x := by
    have := le_integral_of_one_le_on (g := fun x => g x) g.continuous (fun x => (hgmem x).1)
      (c := a + δ) (d := b - δ) (by linarith) (by linarith) (by linarith)
      (fun x hx => by
        have h := hg1 hx
        simp only [Pi.one_apply] at h
        simp [h])
    linarith [this]
  have hev : ∀ᶠ N : ℕ in atTop,
      (∫ x in (0 : ℝ)..1, g x) - δ < (∑ n ∈ Finset.range N, g (u n)) / N :=
    Filter.Tendsto.eventually_const_lt (by linarith) (hequi (fun x => g x) g.continuous)
  filter_upwards [hev, eventually_gt_atTop 0] with N hN hN0
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hcount : ∑ n ∈ Finset.range N, g (u n) ≤ (configCount u (Ico a b) N : ℝ) :=
    sum_le_configCount u _ N _ (fun x => (hgmem x).2)
      (fun x hx => by
        refine hg0 ?_
        intro hx'
        exact hx ⟨le_of_lt hx'.1, hx'.2⟩)
  have : (∑ n ∈ Finset.range N, g (u n)) / N ≤ (configCount u (Ico a b) N : ℝ) / N := by
    gcongr
  linarith [hN, this]

/-- **Configuration counting density from equidistribution.**

If `u` is equidistributed in `[0,1]` (against continuous test functions) then, for any
subinterval `[a, b) ⊆ [0, 1]`, the proportion of indices `n < N` with `u n ∈ [a, b)` tends to
`b - a`.  This is the reduction from continuous test functions to the basic test functions of
bounded variation, namely indicators of intervals. -/
theorem configCount_density_of_BV (u : ℕ → ℝ) (hequi : Equidistributed u) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ => (configCount u (Ico a b) N : ℝ) / N) atTop (𝓝 (b - a)) := by
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  have hδ : 0 < ε / 4 := by linarith
  have hup := eventually_configCount_div_le u hequi hab hδ
  have hlo := eventually_le_configCount_div u hequi ha hb hδ
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hup.and hlo)
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN₀ n hn
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end EquidistributionBVReduction
end Brockian

