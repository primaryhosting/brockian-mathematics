import Mathlib

/-!
# Config Count Density Of BV
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_density_of_BV
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

set_option grind.warning false

namespace Brockian
namespace EquidistributionBVReduction

open Filter Set MeasureTheory
open scoped Topology

/-- `configCount f x N` is the number of the first `N` points of the sequence `x`, each
configuration `x n` being counted with the weight `f (x n)`. -/
noncomputable def configCount (f : ℝ → ℝ) (x : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, f (x n)

/-- A sequence `x : ℕ → ℝ` taking values in `[0,1)` is *equidistributed* if, for every
subinterval `[a, b) ⊆ [0, 1]`, the proportion of the first `N` terms lying in `[a, b)`
converges to the length `b - a` of the interval. -/
def Equidistributed (x : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    Tendsto (fun N : ℕ => (((Finset.range N).filter fun n => x n ∈ Ico a b).card : ℝ) / N)
      atTop (𝓝 (b - a))

/-- `countIn x m i N` is the number of the first `N` points of `x` lying in the `i`-th interval
`[i/m, (i+1)/m)` of the `m`-adic subdivision of `[0,1)`. -/
noncomputable def countIn (x : ℕ → ℝ) (m i N : ℕ) : ℝ :=
  (((Finset.range N).filter fun n => x n ∈ Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m)).card : ℝ)

section Aux

variable {x : ℕ → ℝ}

lemma floor_eq_iff_mem_Ico {m : ℕ} (hm : 0 < m) {y : ℝ} (hy : 0 ≤ y) (i : ℕ) :
    ⌊(m : ℝ) * y⌋₊ = i ↔ y ∈ Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [Nat.floor_eq_iff (by positivity), Set.mem_Ico, div_le_iff₀ hm', lt_div_iff₀ hm']
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith

/-- Endpoints of the `m`-adic subdivision lie in `[0,1]`. -/
lemma div_mem_Icc {m i : ℕ} (hm : 0 < m) (hi : i ≤ m) : ((i : ℝ) / m) ∈ Icc (0:ℝ) 1 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hi' : (i : ℝ) ≤ m := by exact_mod_cast hi
  constructor
  · positivity
  · rw [div_le_one hm']; exact hi'

lemma succ_div_mem_Icc {m i : ℕ} (hm : 0 < m) (hi : i < m) :
    (((i : ℝ) + 1) / m) ∈ Icc (0:ℝ) 1 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hi' : (i : ℝ) + 1 ≤ m := by exact_mod_cast hi
  constructor
  · positivity
  · rw [div_le_one hm']; exact hi'

lemma div_le_succ_div {m i : ℕ} (hm : 0 < m) : (i : ℝ) / m ≤ ((i : ℝ) + 1) / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h : ((i : ℝ) + 1) / m - (i : ℝ) / m = 1 / m := by field_simp; ring
  have h2 : (0 : ℝ) < 1 / m := by positivity
  linarith

/-- Splitting the first `N` points according to which of the `m` intervals `[i/m, (i+1)/m)`
they belong to. -/
lemma sum_eq_sum_over_intervals {g : ℝ → ℝ} (hx : ∀ n, x n ∈ Ico (0:ℝ) 1) {m : ℕ} (hm : 0 < m)
    (N : ℕ) :
    ∑ n ∈ Finset.range N, g (x n)
      = ∑ i ∈ Finset.range m, ∑ n ∈ (Finset.range N).filter
          (fun n => x n ∈ Ico ((i : ℝ) / m) (((i : ℝ) + 1) / m)), g (x n) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmaps : ∀ n ∈ Finset.range N, ⌊(m : ℝ) * x n⌋₊ ∈ Finset.range m := by
    intro n _
    have h1 : x n < 1 := (hx n).2
    have h0 : (0:ℝ) ≤ x n := (hx n).1
    refine Finset.mem_range.2 ?_
    have hlt : (m : ℝ) * x n < m := by nlinarith
    exact (Nat.floor_lt (by positivity)).2 hlt
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun n => g (x n))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr ?_ (fun n _ => rfl)
  refine Finset.filter_congr (fun n _ => ?_)
  simpa using floor_eq_iff_mem_Ico hm (hx n).1 i

end Aux

section Monotone

variable {x : ℕ → ℝ} {g : ℝ → ℝ}

/-- The integral over `[0,1]` split as a sum of integrals over the `m` intervals
`[i/m, (i+1)/m]`. -/
lemma integral_eq_sum_subintervals (hg : MonotoneOn g (Icc (0:ℝ) 1)) {m : ℕ} (hm : 0 < m) :
    (∫ t in (0:ℝ)..1, g t)
      = ∑ i ∈ Finset.range m, ∫ t in ((i : ℝ) / m)..(((i : ℝ) + 1) / m), g t := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hint : ∀ k, k < m → IntervalIntegrable g volume ((k : ℝ) / m) (((k : ℕ) + 1 : ℕ) / m) := by
    intro k hk
    have hcast : (((k : ℕ) + 1 : ℕ) : ℝ) / m = ((k : ℝ) + 1) / m := by push_cast; ring
    rw [hcast]
    have hsub : uIcc ((k : ℝ) / m) (((k : ℝ) + 1) / m) ⊆ Icc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le (div_le_succ_div hm)]
      exact Set.Icc_subset_Icc (div_mem_Icc hm (le_of_lt hk)).1 (succ_div_mem_Icc hm hk).2
    exact (hg.mono hsub).intervalIntegrable
  have key := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i : ℕ => (i : ℝ) / m) (f := g) (μ := volume) (n := m) hint
  simp only [] at key
  rw [Nat.cast_zero, zero_div, div_self (ne_of_gt hm')] at key
  rw [← key]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  push_cast
  ring_nf

/-- On each subinterval of the subdivision, the integral is squeezed between the values of the
monotone function at the endpoints. -/
lemma subinterval_bounds (hg : MonotoneOn g (Icc (0:ℝ) 1)) {m : ℕ} (hm : 0 < m) {i : ℕ}
    (hi : i < m) :
    g ((i : ℝ) / m) * (1 / m) ≤ (∫ t in ((i : ℝ) / m)..(((i : ℝ) + 1) / m), g t)
      ∧ (∫ t in ((i : ℝ) / m)..(((i : ℝ) + 1) / m), g t) ≤ g (((i : ℝ) + 1) / m) * (1 / m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hle : (i : ℝ) / m ≤ ((i : ℝ) + 1) / m := div_le_succ_div hm
  have hsub : uIcc ((i : ℝ) / m) (((i : ℝ) + 1) / m) ⊆ Icc (0:ℝ) 1 := by
    rw [Set.uIcc_of_le hle]
    exact Set.Icc_subset_Icc (div_mem_Icc hm (le_of_lt hi)).1 (succ_div_mem_Icc hm hi).2
  have hsub' : Icc ((i : ℝ) / m) (((i : ℝ) + 1) / m) ⊆ Icc (0:ℝ) 1 := by
    rw [← Set.uIcc_of_le hle]; exact hsub
  have hgint : IntervalIntegrable g volume ((i : ℝ) / m) (((i : ℝ) + 1) / m) :=
    (hg.mono hsub).intervalIntegrable
  have hwidth : ((i : ℝ) + 1) / m - (i : ℝ) / m = 1 / m := by field_simp; ring
  have hlo : ∀ t ∈ Icc ((i : ℝ) / m) (((i : ℝ) + 1) / m), g ((i : ℝ) / m) ≤ g t := fun t ht =>
    hg (div_mem_Icc hm (le_of_lt hi)) (hsub' ht) ht.1
  have hhi : ∀ t ∈ Icc ((i : ℝ) / m) (((i : ℝ) + 1) / m), g t ≤ g (((i : ℝ) + 1) / m) := fun t ht =>
    hg (hsub' ht) (succ_div_mem_Icc hm hi) ht.2
  constructor
  · have hmono := intervalIntegral.integral_mono_on (f := fun _ : ℝ => g ((i : ℝ) / m)) (g := g)
      hle intervalIntegrable_const hgint hlo
    calc g ((i : ℝ) / m) * (1 / m)
        = (((i : ℝ) + 1) / m - (i : ℝ) / m) • g ((i : ℝ) / m) := by
          rw [hwidth, smul_eq_mul, mul_comm]
      _ ≤ _ := by rw [← intervalIntegral.integral_const]; exact hmono
  · have hmono := intervalIntegral.integral_mono_on (f := g)
      (g := fun _ : ℝ => g (((i : ℝ) + 1) / m)) hle hgint intervalIntegrable_const hhi
    calc (∫ t in ((i : ℝ) / m)..(((i : ℝ) + 1) / m), g t)
        ≤ (((i : ℝ) + 1) / m - (i : ℝ) / m) • g (((i : ℝ) + 1) / m) := by
          rw [← intervalIntegral.integral_const]; exact hmono
      _ = g (((i : ℝ) + 1) / m) * (1 / m) := by rw [hwidth, smul_eq_mul, mul_comm]

/-- Lower and upper Riemann-type bounds for the weighted count. -/
lemma sum_bounds (hx : ∀ n, x n ∈ Ico (0:ℝ) 1) (hg : MonotoneOn g (Icc (0:ℝ) 1)) {m : ℕ}
    (hm : 0 < m) (N : ℕ) :
    ∑ i ∈ Finset.range m, g ((i : ℝ) / m) * countIn x m i N
      ≤ ∑ n ∈ Finset.range N, g (x n)
    ∧ ∑ n ∈ Finset.range N, g (x n)
      ≤ ∑ i ∈ Finset.range m, g (((i : ℝ) + 1) / m) * countIn x m i N := by
  simp only [countIn]
  rw [sum_eq_sum_over_intervals hx hm N]
  constructor
  · refine Finset.sum_le_sum (fun i hi => ?_)
    have hi' : i < m := Finset.mem_range.1 hi
    have hbound : ∀ n ∈ (Finset.range N).filter
        (fun n => x n ∈ Ico ((i:ℝ)/m) (((i:ℝ)+1)/m)), g ((i : ℝ) / m) ≤ g (x n) := by
      intro n hn
      have hmem := (Finset.mem_filter.1 hn).2
      exact hg (div_mem_Icc hm (le_of_lt hi')) ⟨(hx n).1, le_of_lt (hx n).2⟩ hmem.1
    have := Finset.card_nsmul_le_sum _ _ _ hbound
    simpa [nsmul_eq_mul, mul_comm] using this
  · refine Finset.sum_le_sum (fun i hi => ?_)
    have hi' : i < m := Finset.mem_range.1 hi
    have hbound : ∀ n ∈ (Finset.range N).filter
        (fun n => x n ∈ Ico ((i:ℝ)/m) (((i:ℝ)+1)/m)), g (x n) ≤ g (((i : ℝ) + 1) / m) := by
      intro n hn
      have hmem := (Finset.mem_filter.1 hn).2
      exact hg ⟨(hx n).1, le_of_lt (hx n).2⟩ (succ_div_mem_Icc hm hi') (le_of_lt hmem.2)
    have := Finset.sum_le_card_nsmul _ _ _ hbound
    simpa [nsmul_eq_mul, mul_comm] using this

lemma tendsto_avg_of_monotoneOn (hx : ∀ n, x n ∈ Ico (0:ℝ) 1) (hequi : Equidistributed x)
    (hg : MonotoneOn g (Icc (0:ℝ) 1)) :
    Tendsto (fun N : ℕ => configCount g x N / N) atTop (𝓝 (∫ t in (0:ℝ)..1, g t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Choose a subdivision fine enough that the total oscillation is at most `ε/4`.
  obtain ⟨m0, hm0⟩ := exists_nat_gt (4 * (g 1 - g 0) / ε)
  obtain ⟨m, hm, hmgt⟩ : ∃ m : ℕ, 0 < m ∧ 4 * (g 1 - g 0) / ε < m :=
    ⟨m0 + 1, Nat.succ_pos _, lt_trans hm0 (by exact_mod_cast Nat.lt_succ_self m0)⟩
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hdiff : (g 1 - g 0) / m < ε / 4 := by
    rw [div_lt_iff₀ hε] at hmgt
    rw [div_lt_div_iff₀ hm' (by norm_num : (0:ℝ) < 4)]
    nlinarith
  -- The lower and upper Riemann sums of the subdivision.
  have hUL : (∑ i ∈ Finset.range m, g (((i:ℝ)+1)/m) * (1/m))
      - (∑ i ∈ Finset.range m, g ((i:ℝ)/m) * (1/m)) = (g 1 - g 0) / m := by
    rw [← Finset.sum_sub_distrib]
    have hterm : ∀ i ∈ Finset.range m, g (((i:ℝ)+1)/m) * (1/m) - g ((i:ℝ)/m) * (1/m)
        = (1/(m:ℝ)) * ((fun j : ℕ => g ((j:ℝ)/m)) (i+1) - (fun j : ℕ => g ((j:ℝ)/m)) i) := by
      intro i _
      simp only []
      push_cast
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
      Finset.sum_range_sub (fun j : ℕ => g ((j:ℝ)/m))]
    rw [Nat.cast_zero, zero_div, div_self (ne_of_gt hm')]
    ring
  have hLI : (∑ i ∈ Finset.range m, g ((i:ℝ)/m) * (1/m)) ≤ ∫ t in (0:ℝ)..1, g t := by
    rw [integral_eq_sum_subintervals hg hm]
    exact Finset.sum_le_sum (fun i hi => (subinterval_bounds hg hm (Finset.mem_range.1 hi)).1)
  have hIU : (∫ t in (0:ℝ)..1, g t) ≤ ∑ i ∈ Finset.range m, g (((i:ℝ)+1)/m) * (1/m) := by
    rw [integral_eq_sum_subintervals hg hm]
    exact Finset.sum_le_sum (fun i hi => (subinterval_bounds hg hm (Finset.mem_range.1 hi)).2)
  -- Equidistribution: each interval of the subdivision gets a proportion `1/m` of the points.
  have hcount : ∀ i ∈ Finset.range m,
      Tendsto (fun N : ℕ => countIn x m i N / N) atTop (𝓝 (1/m)) := by
    intro i hi
    have hi' : i < m := Finset.mem_range.1 hi
    have h := hequi ((i:ℝ)/m) (((i:ℝ)+1)/m) (div_mem_Icc hm (le_of_lt hi')).1
      (div_le_succ_div hm) (succ_div_mem_Icc hm hi').2
    have hw : ((i:ℝ)+1)/m - (i:ℝ)/m = 1/m := by field_simp; ring
    rw [hw] at h
    exact h
  have hlow : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range m, g ((i:ℝ)/m) * (countIn x m i N / N))
      atTop (𝓝 (∑ i ∈ Finset.range m, g ((i:ℝ)/m) * (1/m))) :=
    tendsto_finset_sum _ (fun i hi => (hcount i hi).const_mul (g ((i:ℝ)/m)))
  have hupp : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range m, g (((i:ℝ)+1)/m) * (countIn x m i N / N))
      atTop (𝓝 (∑ i ∈ Finset.range m, g (((i:ℝ)+1)/m) * (1/m))) :=
    tendsto_finset_sum _ (fun i hi => (hcount i hi).const_mul (g (((i:ℝ)+1)/m)))
  rw [Metric.tendsto_atTop] at hlow hupp
  obtain ⟨N1, hN1⟩ := hlow (ε/4) (by linarith)
  obtain ⟨N2, hN2⟩ := hupp (ε/4) (by linarith)
  refine ⟨max 1 (max N1 N2), fun N hN => ?_⟩
  have hN0 : 0 < N := lt_of_lt_of_le Nat.one_pos (le_trans (le_max_left _ _) hN)
  have hNR : (0:ℝ) < N := by exact_mod_cast hN0
  have h1 := hN1 N (le_trans (le_trans (le_max_left N1 N2) (le_max_right 1 _)) hN)
  have h2 := hN2 N (le_trans (le_trans (le_max_right N1 N2) (le_max_right 1 _)) hN)
  rw [Real.dist_eq, abs_lt] at h1 h2
  obtain ⟨hb1, hb2⟩ := sum_bounds hx hg hm N
  have hsplit1 : (∑ i ∈ Finset.range m, g ((i:ℝ)/m) * countIn x m i N) / N
      = ∑ i ∈ Finset.range m, g ((i:ℝ)/m) * (countIn x m i N / N) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun i _ => mul_div_assoc _ _ _)
  have hsplit2 : (∑ i ∈ Finset.range m, g (((i:ℝ)+1)/m) * countIn x m i N) / N
      = ∑ i ∈ Finset.range m, g (((i:ℝ)+1)/m) * (countIn x m i N / N) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun i _ => mul_div_assoc _ _ _)
  have hlower : (∑ i ∈ Finset.range m, g ((i:ℝ)/m) * (countIn x m i N / N))
      ≤ configCount g x N / N := by
    rw [← hsplit1, configCount]
    gcongr
  have hupper : configCount g x N / N
      ≤ ∑ i ∈ Finset.range m, g (((i:ℝ)+1)/m) * (countIn x m i N / N) := by
    rw [← hsplit2, configCount]
    gcongr
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end Monotone

/-- **Equidistribution / bounded-variation reduction.**  If `x` is a sequence in `[0,1)` which
is equidistributed (each subinterval `[a,b)` receives its fair share `b - a` of the points),
then for every weight `f` of bounded variation on `[0,1]` the weighted configuration count
`configCount f x N` has density `∫₀¹ f`. -/
theorem configCount_density_of_BV {x : ℕ → ℝ} (hx : ∀ n, x n ∈ Ico (0:ℝ) 1)
    (hequi : Equidistributed x) {f : ℝ → ℝ} (hf : BoundedVariationOn f (Icc (0:ℝ) 1)) :
    Tendsto (fun N : ℕ => configCount f x N / N) atTop (𝓝 (∫ t in (0:ℝ)..1, f t)) := by
  obtain ⟨p, q, hp, hq, rfl⟩ := hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have huIcc : uIcc (0:ℝ) 1 = Icc (0:ℝ) 1 := Set.uIcc_of_le (by norm_num)
  have hpi : IntervalIntegrable p volume 0 1 := by
    refine MonotoneOn.intervalIntegrable ?_
    rw [huIcc]; exact hp
  have hqi : IntervalIntegrable q volume 0 1 := by
    refine MonotoneOn.intervalIntegrable ?_
    rw [huIcc]; exact hq
  have hfun : (fun N : ℕ => configCount (p - q) x N / N)
      = fun N : ℕ => configCount p x N / N - configCount q x N / N := by
    funext N
    simp only [configCount, Pi.sub_apply, Finset.sum_sub_distrib, sub_div]
  have hint : (∫ t in (0:ℝ)..1, (p - q) t) = (∫ t in (0:ℝ)..1, p t) - ∫ t in (0:ℝ)..1, q t := by
    simp only [Pi.sub_apply]
    exact intervalIntegral.integral_sub hpi hqi
  rw [hfun, hint]
  exact (tendsto_avg_of_monotoneOn hx hequi hp).sub (tendsto_avg_of_monotoneOn hx hequi hq)

/-- Unweighted form of the reduction: if the indicator function of a measurable set `A` has
bounded variation on `[0,1]`, then the proportion of the first `N` points of an equidistributed
sequence that land in `A` converges to the measure of `A ∩ (0,1]`. -/
theorem configCount_indicator_density_of_BV {x : ℕ → ℝ} (hx : ∀ n, x n ∈ Ico (0:ℝ) 1)
    (hequi : Equidistributed x) {A : Set ℝ} (hA : MeasurableSet A)
    (hBV : BoundedVariationOn (A.indicator (fun _ => (1:ℝ))) (Icc (0:ℝ) 1)) :
    Tendsto (fun N : ℕ => (((Finset.range N).filter fun n => x n ∈ A).card : ℝ) / N) atTop
      (𝓝 (volume (A ∩ Ioc (0:ℝ) 1)).toReal) := by
  have hcount : ∀ N : ℕ, configCount (A.indicator (fun _ => (1:ℝ))) x N
      = (((Finset.range N).filter fun n => x n ∈ A).card : ℝ) := by
    intro N
    simp [configCount, Set.indicator_apply]
  have hint : (∫ t in (0:ℝ)..1, A.indicator (fun _ => (1:ℝ)) t)
      = (volume (A ∩ Ioc (0:ℝ) 1)).toReal := by
    rw [intervalIntegral.integral_of_le zero_le_one,
      MeasureTheory.setIntegral_indicator hA, MeasureTheory.setIntegral_const,
      Set.inter_comm]
    simp [MeasureTheory.measureReal_def]
  have := configCount_density_of_BV hx hequi hBV
  rw [hint] at this
  simpa only [hcount] using this

end EquidistributionBVReduction
end Brockian

