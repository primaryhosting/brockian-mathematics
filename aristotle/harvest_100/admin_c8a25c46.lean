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
# Reduction of equidistribution to bounded-variation test functions

Let `x : ℕ → ℝ` be a sequence.  Assume that for **every** real function `f` of bounded
variation on `[0,1]` the Birkhoff-type averages

`(1/N) * ∑_{n < N} f (Int.fract (x n))`

converge to `∫₀¹ f`.  We show that the sequence `x` is then equidistributed modulo one, and
moreover *uniformly* so: the counting error over intervals `[a,b) ⊆ [0,1]` tends to `0`
uniformly in the endpoints (i.e. the discrepancy of the sequence tends to `0`).

The main statement is `equidistribution_of_BV_uniform`.  It is unconditional: apart from the
assumption on the sequence itself, no auxiliary result is taken as a hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set MeasureTheory
open scoped Topology

namespace Brockian

open scoped Classical in
/-- The number of indices `n < N` for which the fractional part of `x n` lies in `[a, b)`. -/
noncomputable def cnt (x : ℕ → ℝ) (N : ℕ) (a b : ℝ) : ℕ :=
  ((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card

/-- The (normalized) counting function of the sequence: the proportion of the first `N`
fractional parts that lie in `[a, b)`. -/
noncomputable def freq (x : ℕ → ℝ) (N : ℕ) (a b : ℝ) : ℝ := (cnt x N a b : ℝ) / N

/-- The indicator function of the interval `[a, b)`, as a real-valued function. -/
noncomputable def indIco (a b : ℝ) : ℝ → ℝ := fun t => if t ∈ Set.Ico a b then (1 : ℝ) else 0

/-! ### Bounded variation of interval indicators -/

/-- Variation is subadditive. -/
theorem eVariationOn_add_le (f g : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun t => f t + g t) s ≤ eVariationOn f s + eVariationOn g s := by
  refine iSup_le ?_
  rintro ⟨n, ⟨u, hu, us⟩⟩
  have key : ∀ i, edist (f (u (i + 1)) + g (u (i + 1))) (f (u i) + g (u i))
      ≤ edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i)) := by
    intro i
    simp only [edist_dist, Real.dist_eq]
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    calc |f (u (i + 1)) + g (u (i + 1)) - (f (u i) + g (u i))|
        = |(f (u (i + 1)) - f (u i)) + (g (u (i + 1)) - g (u i))| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  calc ∑ i ∈ Finset.range n, edist (f (u (i + 1)) + g (u (i + 1))) (f (u i) + g (u i))
      ≤ ∑ i ∈ Finset.range n,
          (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) :=
        Finset.sum_le_sum fun i _ => key i
    _ = (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)))
        + ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (eVariationOn.sum_le f n hu us) (eVariationOn.sum_le g n hu us)

/-- Variation is invariant under negation. -/
theorem eVariationOn_neg (f : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun t => -f t) s = eVariationOn f s := by
  unfold eVariationOn
  congr 1 with p : 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [edist_dist, Real.dist_eq, abs_sub_comm]

/-- The step function `t ↦ if a ≤ t then 1 else 0` has bounded variation on `[0,1]`. -/
theorem boundedVariationOn_step (a : ℝ) :
    BoundedVariationOn (fun t : ℝ => if a ≤ t then (1 : ℝ) else 0) (Set.Icc 0 1) := by
  have hmono : MonotoneOn (fun t : ℝ => if a ≤ t then (1 : ℝ) else 0) (Set.Icc (0:ℝ) 1) := by
    intro s _ t _ hst
    dsimp only
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact absurd (h1.trans hst) h2
    · norm_num
    · exact le_rfl
  have h2 := hmono.eVariationOn_le (a := (0:ℝ)) (b := (1:ℝ)) (by norm_num) (by norm_num)
  rw [Set.inter_self] at h2
  exact (h2.trans_lt ENNReal.ofReal_lt_top).ne

/-- The indicator of an interval has bounded variation on `[0,1]`. -/
theorem boundedVariationOn_indIco {a b : ℝ} (hab : a ≤ b) :
    BoundedVariationOn (indIco a b) (Set.Icc 0 1) := by
  have heq : indIco a b = fun t : ℝ =>
      (if a ≤ t then (1:ℝ) else 0) + (-(if b ≤ t then (1:ℝ) else 0)) := by
    funext t
    simp only [indIco, Set.mem_Ico]
    rcases le_or_gt a t with h1 | h1
    · rcases le_or_gt b t with h2 | h2
      · rw [if_neg (fun hc => absurd hc.2 (not_lt.2 h2)), if_pos h1, if_pos h2]; ring
      · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_neg (not_le.2 h2)]; ring
    · rw [if_neg (fun hc => absurd hc.1 (not_le.2 h1)), if_neg (not_le.2 h1),
        if_neg (not_le.2 (lt_of_lt_of_le h1 hab))]; ring
  rw [BoundedVariationOn, heq]
  refine ne_top_of_le_ne_top ?_ (eVariationOn_add_le _ _ _)
  rw [eVariationOn_neg]
  exact ENNReal.add_ne_top.2 ⟨boundedVariationOn_step a, boundedVariationOn_step b⟩

/-- The integral of the indicator of `[a,b) ⊆ [0,1]` over `[0,1]` is `b - a`. -/
theorem integral_indIco {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ t in (0:ℝ)..1, indIco a b t) = b - a := by
  have hind : indIco a b = Set.indicator (Set.Ico a b) (fun _ => (1:ℝ)) := by
    funext t; simp [indIco, Set.indicator_apply]
  have hsub : Set.Ioo a b ⊆ Set.Ioc (0:ℝ) 1 ∩ Set.Ico a b := by
    intro t ht
    exact ⟨⟨lt_of_le_of_lt ha ht.1, ht.2.le.trans hb⟩, ⟨ht.1.le, ht.2⟩⟩
  have h1 : volume (Set.Ioc (0:ℝ) 1 ∩ Set.Ico a b) = ENNReal.ofReal (b - a) := by
    apply le_antisymm
    · calc volume (Set.Ioc (0:ℝ) 1 ∩ Set.Ico a b) ≤ volume (Set.Icc a b) :=
            measure_mono (fun t ht => ⟨ht.2.1, ht.2.2.le⟩)
        _ = ENNReal.ofReal (b - a) := by rw [Real.volume_Icc]
    · calc ENNReal.ofReal (b - a) = volume (Set.Ioo a b) := by rw [Real.volume_Ioo]
        _ ≤ _ := measure_mono hsub
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), hind,
    MeasureTheory.setIntegral_indicator measurableSet_Ico]
  simp only [MeasureTheory.integral_const, smul_eq_mul, mul_one,
    MeasureTheory.measureReal_def, MeasureTheory.Measure.restrict_apply_univ]
  rw [h1, ENNReal.toReal_ofReal (by linarith)]

/-- The Birkhoff sum of an interval indicator is the corresponding counting function. -/
theorem sum_indIco (x : ℕ → ℝ) (N : ℕ) (a b : ℝ) :
    (∑ n ∈ Finset.range N, indIco a b (Int.fract (x n))) = (cnt x N a b : ℝ) := by
  classical
  simp [indIco, cnt]

/-! ### Pointwise equidistribution -/

/-- Under the bounded-variation hypothesis, the frequency of `[a,b)` converges to `b - a`. -/
theorem tendsto_freq (x : ℕ → ℝ)
    (h : ∀ f : ℝ → ℝ, BoundedVariationOn f (Set.Icc (0:ℝ) 1) →
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (Int.fract (x n))) / N) atTop
        (𝓝 (∫ t in (0:ℝ)..1, f t)))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ => freq x N a b) atTop (𝓝 (b - a)) := by
  have := h (indIco a b) (boundedVariationOn_indIco hab)
  rw [integral_indIco ha hab hb] at this
  simpa only [freq, sum_indIco] using this

/-! ### From pointwise to uniform -/

/-- The counting function is monotone in the right endpoint (with left endpoint `0`). -/
theorem cnt_mono (x : ℕ → ℝ) (N : ℕ) {s t : ℝ} (hst : s ≤ t) :
    cnt x N 0 s ≤ cnt x N 0 t := by
  classical
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Set.mem_Ico] at *
  exact ⟨hn.1, hn.2.1, hn.2.2.trans_le hst⟩

/-- Splitting the counting function at an intermediate point. -/
theorem cnt_split (x : ℕ → ℝ) (N : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    cnt x N 0 b = cnt x N 0 a + cnt x N a b := by
  classical
  unfold cnt
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext n
    simp only [Finset.mem_union, Finset.mem_filter, Set.mem_Ico]
    constructor
    · rintro ⟨hn, h0, hb⟩
      rcases lt_or_ge (Int.fract (x n)) a with hlt | hge
      · exact Or.inl ⟨hn, h0, hlt⟩
      · exact Or.inr ⟨hn, hge, hb⟩
    · rintro (⟨hn, h0, hb⟩ | ⟨hn, h0, hb⟩)
      · exact ⟨hn, h0, hb.trans_le hab⟩
      · exact ⟨hn, ha.trans h0, hb⟩
  · rw [Finset.disjoint_left]
    intro n hn hn'
    simp only [Finset.mem_filter, Set.mem_Ico] at hn hn'
    exact absurd hn'.2.1 (not_le.2 hn.2.2)

/-- Monotonicity of the normalized counting function in the right endpoint. -/
theorem freq_mono (x : ℕ → ℝ) (N : ℕ) {s t : ℝ} (hst : s ≤ t) :
    freq x N 0 s ≤ freq x N 0 t := by
  have := cnt_mono x N hst
  unfold freq
  gcongr

/-- Every point of `[0,1]` lies in a grid interval `[j/K, (j+1)/K]` with `j + 1 ≤ K`. -/
theorem grid_bracket (K : ℕ) (hK : 1 ≤ K) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ j : ℕ, j + 1 ≤ K ∧ (j:ℝ)/K ≤ t ∧ t ≤ ((j:ℝ)+1)/K := by
  have hKR : (0:ℝ) < K := by exact_mod_cast hK
  set j := ⌊t * K⌋₊ with hj
  have hfl : (j:ℝ) ≤ t * K := Nat.floor_le (by positivity)
  have hfl2 : t * K < j + 1 := Nat.lt_floor_add_one _
  by_cases hjK : j + 1 ≤ K
  · exact ⟨j, hjK, by rw [div_le_iff₀ hKR]; exact hfl, by rw [le_div_iff₀ hKR]; exact hfl2.le⟩
  · have hKj : K ≤ j := by omega
    have h1 : (K:ℝ) ≤ t * K := le_trans (by exact_mod_cast hKj) hfl
    have ht : 1 ≤ t := by nlinarith
    have ht' : t = 1 := le_antisymm ht1 ht
    have hcast : ((K - 1 : ℕ) : ℝ) = (K:ℝ) - 1 := by push_cast [Nat.cast_sub hK]; ring
    refine ⟨K - 1, by omega, ?_, ?_⟩
    · rw [hcast, ht', div_le_one hKR]; linarith
    · rw [hcast, ht', le_div_iff₀ hKR]; linarith

/-- Uniform convergence of the cumulative distribution function on `[0,1]`. -/
theorem uniform_freq_zero (x : ℕ → ℝ)
    (h : ∀ f : ℝ → ℝ, BoundedVariationOn f (Set.Icc (0:ℝ) 1) →
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (Int.fract (x n))) / N) atTop
        (𝓝 (∫ t in (0:ℝ)..1, f t)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → |freq x N 0 t - t| < ε := by
  have hε4 : 0 < ε / 4 := by linarith
  obtain ⟨K, hKgt⟩ := exists_nat_gt (4 / ε)
  have hKR : (0:ℝ) < K := lt_of_le_of_lt (by positivity) hKgt
  have hK1 : 1 ≤ K := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by
    rintro rfl; simp at hKR)
  have hKinv : 1 / (K:ℝ) < ε / 4 := by
    rw [div_lt_iff₀ hKR]
    rw [div_lt_iff₀ hε] at hKgt
    nlinarith
  -- convergence at the grid points
  have hpt : ∀ j : ℕ, ∃ M : ℕ, ∀ N ≥ M,
      |freq x N 0 (min ((j:ℝ)/K) 1) - min ((j:ℝ)/K) 1| < ε / 4 := by
    intro j
    have hb0 : (0:ℝ) ≤ min ((j:ℝ)/K) 1 := le_min (by positivity) zero_le_one
    have hb1 : min ((j:ℝ)/K) 1 ≤ 1 := min_le_right _ _
    have hten := tendsto_freq x h (le_refl (0:ℝ)) hb0 hb1
    rw [Metric.tendsto_atTop] at hten
    obtain ⟨M, hM⟩ := hten (ε / 4) hε4
    exact ⟨M, fun N hN => by simpa [Real.dist_eq, sub_zero] using hM N hN⟩
  choose M hM using hpt
  refine ⟨max 1 ((Finset.range (K + 1)).sup M), le_max_left _ _, ?_⟩
  intro N hN t ht0 ht1
  obtain ⟨j, hjK, hlo, hhi⟩ := grid_bracket K hK1 t ht0 ht1
  have hjle : (j:ℝ) / K ≤ 1 := by
    rw [div_le_one hKR]
    exact_mod_cast Nat.le_of_succ_le hjK
  have hj1le : ((j:ℝ) + 1) / K ≤ 1 := by
    rw [div_le_one hKR]
    exact_mod_cast hjK
  have hgj : min ((j:ℝ)/K) 1 = (j:ℝ)/K := min_eq_left hjle
  have hgj1 : min (((j + 1 : ℕ):ℝ)/K) 1 = ((j:ℝ) + 1)/K := by
    push_cast
    exact min_eq_left hj1le
  have hsupj : M j ≤ N :=
    le_trans (Finset.le_sup (Finset.mem_range.2 (by omega))) (le_trans (le_max_right _ _) hN)
  have hsupj1 : M (j + 1) ≤ N :=
    le_trans (Finset.le_sup (Finset.mem_range.2 (by omega))) (le_trans (le_max_right _ _) hN)
  have hA := hM j N hsupj
  have hB := hM (j + 1) N hsupj1
  rw [hgj] at hA
  rw [hgj1] at hB
  rw [abs_lt] at hA hB ⊢
  have hmono1 : freq x N 0 ((j:ℝ)/K) ≤ freq x N 0 t := freq_mono x N hlo
  have hmono2 : freq x N 0 t ≤ freq x N 0 (((j:ℝ) + 1)/K) := freq_mono x N hhi
  have hstep : ((j:ℝ) + 1)/K = (j:ℝ)/K + 1/K := by ring
  exact ⟨by linarith, by linarith⟩

/-! ### Main theorem -/

/-- **Equidistribution from bounded-variation test functions, uniformly in the interval.**

If for every function `f` of bounded variation on `[0,1]` the averages
`(1/N) ∑_{n<N} f (Int.fract (x n))` converge to `∫₀¹ f`, then the sequence `x` is
equidistributed modulo one, uniformly over all subintervals `[a,b) ⊆ [0,1]`; equivalently,
the discrepancy of `x` tends to `0`. -/
theorem equidistribution_of_BV_uniform (x : ℕ → ℝ)
    (h : ∀ f : ℝ → ℝ, BoundedVariationOn f (Set.Icc (0:ℝ) 1) →
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (Int.fract (x n))) / N) atTop
        (𝓝 (∫ t in (0:ℝ)..1, f t)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      |freq x N a b - (b - a)| < ε := by
  obtain ⟨N₀, hN₀, hmain⟩ := uniform_freq_zero x h (half_pos hε)
  refine ⟨N₀, fun N hN a b ha hab hb => ?_⟩
  have hNpos : (0:ℝ) < N := by
    have : 1 ≤ N := le_trans hN₀ hN
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hsplit : freq x N a b = freq x N 0 b - freq x N 0 a := by
    unfold freq
    rw [cnt_split x N ha hab]
    push_cast
    ring
  have h1 := hmain N hN b (ha.trans hab) hb
  have h2 := hmain N hN a ha (hab.trans hb)
  rw [hsplit]
  have : freq x N 0 b - freq x N 0 a - (b - a)
      = (freq x N 0 b - b) - (freq x N 0 a - a) := by ring
  rw [this]
  calc |freq x N 0 b - b - (freq x N 0 a - a)|
      ≤ |freq x N 0 b - b| + |freq x N 0 a - a| := abs_sub _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := by ring

end Brockian

