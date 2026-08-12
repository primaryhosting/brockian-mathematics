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
# Equidistribution: reduction from continuous test functions to BV (indicator) test functions

This file contains the classical "bounded variation reduction" step in the theory of
equidistribution modulo one: if a sequence `x : ℕ → ℝ` is equidistributed mod `1` in Weyl's
sense (Cesàro averages of *continuous* `1`-periodic test functions converge to the mean of the
test function), then the counting density of the "configurations" `n ↦ Int.fract (x n)` lying in
a subinterval `[a, b) ⊆ [0, 1)` converges to the length `b - a`.

The indicator of an interval is the basic example of a function of bounded variation which is not
continuous, so the content of the main theorem is exactly that the class of admissible test
functions may be enlarged from continuous functions to such BV functions.

The main result is `Brockian.EquidistributionBVReduction.configCount_density_of_BV`; it is
unconditional apart from the (necessary) equidistribution hypothesis on the sequence itself.
-/

open Filter Set MeasureTheory
open scoped Topology BigOperators Classical

namespace Brockian.EquidistributionBVReduction

/-- The number of indices `n < N` whose fractional part `Int.fract (x n)` lies in `[a, b)`. -/
noncomputable def configCount (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card

/-- Weyl's notion of equidistribution modulo one: for every continuous `1`-periodic test
function `f`, the Cesàro averages of `f (x n)` converge to the mean value of `f`. -/
def EquidistributedMod1 (x : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Continuous f → Function.Periodic f 1 →
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (x n)) / N) atTop (𝓝 (∫ t in (0:ℝ)..1, f t))

/-- Periodization: the `1`-periodic function agreeing with `f` on `[0, 1)`. -/
noncomputable def periodize (f : ℝ → ℝ) : ℝ → ℝ := fun t => f (Int.fract t)

lemma periodize_apply (f : ℝ → ℝ) (t : ℝ) : periodize f t = f (Int.fract t) := rfl

lemma periodize_periodic (f : ℝ → ℝ) : Function.Periodic (periodize f) 1 := by
  intro t
  simp [periodize, Int.fract_add_one]

lemma periodize_eqOn (f : ℝ → ℝ) (hf : f 0 = f 1) :
    Set.EqOn (periodize f) f (Set.Icc 0 1) := by
  rintro t ⟨ht0, ht1⟩
  rcases eq_or_lt_of_le ht1 with rfl | ht
  · simp [periodize, hf]
  · simp [periodize, Int.fract_eq_self.2 ⟨ht0, ht⟩]

lemma periodize_continuous {f : ℝ → ℝ} (hf : f 0 = f 1) (hc : ContinuousOn f (Set.Icc 0 1)) :
    Continuous (periodize f) := by
  haveI : Fact ((0:ℝ) < 1) := ⟨one_pos⟩
  have key : periodize f = (AddCircle.liftIco 1 0 f) ∘ ((↑) : ℝ → AddCircle (1:ℝ)) := by
    funext t
    have ht : Int.fract t ∈ Set.Ico (0:ℝ) 1 := ⟨Int.fract_nonneg t, Int.fract_lt_one t⟩
    have hcoe : ((Int.fract t : ℝ) : AddCircle (1:ℝ)) = (t : AddCircle (1:ℝ)) := by
      have h0 : ((Int.fract t : ℝ) : AddCircle (1:ℝ)) - (t : AddCircle (1:ℝ)) = 0 := by
        rw [← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
        exact ⟨-⌊t⌋, by rw [Int.fract]; ring⟩
      exact sub_eq_zero.mp h0
    simp only [Function.comp_apply, ← hcoe, periodize]
    exact (AddCircle.liftIco_zero_coe_apply ht).symm
  rw [key]
  exact (AddCircle.liftIco_zero_continuous hf hc).comp continuous_coinduced_rng

/-- The continuous trapezoidal test function: it vanishes outside `(a, b)`, equals `1` on
`[a + d, b - d]` and interpolates linearly in between. -/
noncomputable def trap (a b d t : ℝ) : ℝ := max 0 (min 1 (min ((t - a) / d) ((b - t) / d)))

lemma trap_nonneg (a b d t : ℝ) : 0 ≤ trap a b d t := le_max_left _ _

lemma trap_le_one (a b d t : ℝ) : trap a b d t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma trap_continuous (a b d : ℝ) : Continuous (trap a b d) := by
  unfold trap
  fun_prop

lemma trap_eq_zero_of_le {a b d t : ℝ} (hd : 0 < d) (h : t ≤ a) : trap a b d t = 0 := by
  have h1 : (t - a) / d ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
  have h2 : min 1 (min ((t - a) / d) ((b - t) / d)) ≤ 0 :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) h1)
  simpa [trap] using max_eq_left h2

lemma trap_eq_zero_of_ge {a b d t : ℝ} (hd : 0 < d) (h : b ≤ t) : trap a b d t = 0 := by
  have h1 : (b - t) / d ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
  have h2 : min 1 (min ((t - a) / d) ((b - t) / d)) ≤ 0 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) h1)
  simpa [trap] using max_eq_left h2

lemma trap_eq_one {a b d t : ℝ} (hd : 0 < d) (h1 : a + d ≤ t) (h2 : t ≤ b - d) :
    trap a b d t = 1 := by
  have e1 : (1:ℝ) ≤ (t - a) / d := (le_div_iff₀ hd).2 (by linarith)
  have e2 : (1:ℝ) ≤ (b - t) / d := (le_div_iff₀ hd).2 (by linarith)
  have e3 : min 1 (min ((t - a) / d) ((b - t) / d)) = 1 := min_eq_left (le_min e1 e2)
  simp [trap, e3]

/-- The trapezoid is dominated by the indicator function of `[a, b)`. -/
lemma trap_le_indicator {a b d : ℝ} (hd : 0 < d) (t : ℝ) :
    trap a b d t ≤ (if t ∈ Set.Ico a b then (1:ℝ) else 0) := by
  by_cases h : t ∈ Set.Ico a b
  · simpa [h] using trap_le_one a b d t
  · rw [if_neg h]
    simp only [Set.mem_Ico, not_and_or, not_le, not_lt] at h
    rcases h with h | h
    · exact le_of_eq (trap_eq_zero_of_le hd h.le)
    · exact le_of_eq (trap_eq_zero_of_ge hd h)

/-- Lower bound for the mean value of the trapezoid. -/
lemma trap_integral_lower {a b d : ℝ} (hd : 0 < d) (ha : 0 ≤ a) (hb : b ≤ 1)
    (hab : a + d ≤ b - d) :
    b - a - 2 * d ≤ ∫ t in (0:ℝ)..1, trap a b d t := by
  have hcont : Continuous (trap a b d) := trap_continuous a b d
  have hint : ∀ u v : ℝ, IntervalIntegrable (trap a b d) volume u v :=
    fun u v => hcont.intervalIntegrable u v
  have h1 : (0:ℝ) ≤ a + d := by linarith
  have h2 : b - d ≤ 1 := by linarith
  have hsplit : (∫ t in (0:ℝ)..1, trap a b d t) =
      (∫ t in (0:ℝ)..(a + d), trap a b d t) + (∫ t in (a + d)..(b - d), trap a b d t)
        + (∫ t in (b - d)..1, trap a b d t) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _),
      intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
  have hmid : (∫ t in (a + d)..(b - d), trap a b d t) = b - d - (a + d) := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1:ℝ)) ?_]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact trap_eq_one hd ht.1 ht.2
  have hleft : (0:ℝ) ≤ ∫ t in (0:ℝ)..(a + d), trap a b d t :=
    intervalIntegral.integral_nonneg h1 (fun t _ => trap_nonneg _ _ _ _)
  have hright : (0:ℝ) ≤ ∫ t in (b - d)..1, trap a b d t :=
    intervalIntegral.integral_nonneg h2 (fun t _ => trap_nonneg _ _ _ _)
  rw [hsplit, hmid]
  linarith

lemma configCount_eq_sum (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) :
    ((configCount x a b N : ℕ) : ℝ)
      = ∑ n ∈ Finset.range N, (if Int.fract (x n) ∈ Set.Ico a b then (1:ℝ) else 0) := by
  simp only [configCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]

/-- The three intervals `[0, a)`, `[a, b)`, `[b, 1)` partition `[0, 1)`. -/
lemma configCount_partition (x : ℕ → ℝ) {a b : ℝ} (hab : a ≤ b) (N : ℕ) :
    configCount x 0 a N + configCount x a b N + configCount x b 1 N = N := by
  classical
  simp only [configCount, Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (g := fun _ => 1) ?_, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.card_range]
  intro n _
  have h0 : 0 ≤ Int.fract (x n) := Int.fract_nonneg _
  have h1 : Int.fract (x n) < 1 := Int.fract_lt_one _
  rcases lt_or_ge (Int.fract (x n)) a with h | h
  · have hna : ¬ (a ≤ Int.fract (x n)) := not_le.2 h
    have hb' : ¬ (b ≤ Int.fract (x n)) := fun hc => hna (le_trans hab hc)
    simp [Set.mem_Ico, h0, h, hna, hb']
  · rcases lt_or_ge (Int.fract (x n)) b with h' | h'
    · have hb' : ¬ (b ≤ Int.fract (x n)) := not_le.2 h'
      simp [Set.mem_Ico, h0, h, h', hb', not_lt.2 h]
    · simp [Set.mem_Ico, h0, h1, h, h', not_lt.2 h, not_lt.2 h']

/-- The key lower bound: asymptotically, the count of configurations in `[a, b)` is at least
`(b - a - ε) N`. -/
lemma configCount_eventually_ge {x : ℕ → ℝ} (hx : EquidistributedMod1 x) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (b - a) - ε ≤ (configCount x a b N : ℝ) / N := by
  rcases le_or_gt (b - a) ε with hcase | hcase
  · filter_upwards with N
    have : (0:ℝ) ≤ (configCount x a b N : ℝ) / N :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    linarith
  · set d : ℝ := ε / 4 with hd_def
    have hd : 0 < d := by positivity
    have hmid : a + d ≤ b - d := by simp only [hd_def]; linarith
    set g : ℝ → ℝ := trap a b d with hg_def
    have hg0 : g 0 = g 1 := by
      rw [hg_def, trap_eq_zero_of_le hd ha, trap_eq_zero_of_ge hd hb]
    have hgc : Continuous g := trap_continuous a b d
    set G : ℝ → ℝ := periodize g with hG_def
    have hGc : Continuous G := periodize_continuous hg0 hgc.continuousOn
    have hGp : Function.Periodic G 1 := periodize_periodic g
    have hGint : (∫ t in (0:ℝ)..1, G t) = ∫ t in (0:ℝ)..1, g t := by
      refine intervalIntegral.integral_congr ?_
      rw [Set.uIcc_of_le (zero_le_one)]
      exact periodize_eqOn g hg0
    have hlow : b - a - ε / 2 ≤ ∫ t in (0:ℝ)..1, G t := by
      rw [hGint]
      have h := trap_integral_lower hd ha hb hmid
      simp only [hd_def] at h ⊢
      linarith
    have htend := hx G hGc hGp
    have hgt : (b - a) - ε < ∫ t in (0:ℝ)..1, G t := by linarith
    have hev := htend.eventually_const_lt hgt
    filter_upwards [hev, eventually_gt_atTop 0] with N hN hN0
    have hNpos : (0:ℝ) < N := by exact_mod_cast hN0
    have hsum : (∑ n ∈ Finset.range N, G (x n)) ≤ (configCount x a b N : ℝ) := by
      rw [configCount_eq_sum]
      exact Finset.sum_le_sum fun n _ => trap_le_indicator hd _
    calc (b - a) - ε ≤ (∑ n ∈ Finset.range N, G (x n)) / N := hN.le
      _ ≤ (configCount x a b N : ℝ) / N := by gcongr

lemma configCount_eventually_le {x : ℕ → ℝ} (hx : EquidistributedMod1 x) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (configCount x a b N : ℝ) / N ≤ (b - a) + ε := by
  have h1 := configCount_eventually_ge hx le_rfl ha (le_trans hab hb) (half_pos hε)
  have h2 := configCount_eventually_ge hx (le_trans ha hab) hb le_rfl (half_pos hε)
  filter_upwards [h1, h2, eventually_gt_atTop 0] with N hN1 hN2 hN0
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN0
  have hpart : (configCount x 0 a N : ℝ) + configCount x a b N + configCount x b 1 N = N := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) (configCount_partition x hab N)
  have hdiv : (configCount x 0 a N : ℝ) / N + (configCount x a b N : ℝ) / N
      + (configCount x b 1 N : ℝ) / N = 1 := by
    field_simp
    linarith
  linarith

/-- **Equidistribution implies convergence of configuration densities.**

If `x` is equidistributed modulo one in Weyl's sense (that is, Cesàro averages of continuous
`1`-periodic test functions converge to their mean), then for any subinterval `[a, b) ⊆ [0, 1)`
the density of indices `n < N` with `Int.fract (x n) ∈ [a, b)` tends to `b - a`.

This is the bounded-variation reduction: the (discontinuous, but BV) indicator of an interval is
an admissible test function. -/
theorem configCount_density_of_BV {x : ℕ → ℝ} (hx : EquidistributedMod1 x) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ => (configCount x a b N : ℝ) / N) atTop (𝓝 (b - a)) := by
  refine tendsto_order.2 ⟨fun c hc => ?_, fun c hc => ?_⟩
  · have hε : 0 < (b - a - c) / 2 := by linarith
    filter_upwards [configCount_eventually_ge hx ha hab hb hε] with N hN
    linarith
  · have hε : 0 < (c - (b - a)) / 2 := by linarith
    filter_upwards [configCount_eventually_le hx ha hab hb hε] with N hN
    linarith

end Brockian.EquidistributionBVReduction


