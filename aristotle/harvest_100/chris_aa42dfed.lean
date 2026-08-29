import Mathlib

/-!
# Total Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.total_over_main_tendsto
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

open Filter Finset

/-- The `N`-th equidistributed sample sum of `f`: the total of the values of `f` at the
`N` equidistributed sample points `0/N, 1/N, …, (N-1)/N` of the unit interval. -/
noncomputable def total (f : ℝ → ℝ) (N : ℕ) : ℝ := ∑ k ∈ Finset.range N, f ((k : ℝ) / N)

/-- The main term predicted by equidistribution: `N` times the mean value of `f`
on the unit interval. -/
noncomputable def main (f : ℝ → ℝ) (N : ℕ) : ℝ := (N : ℝ) * ∫ x in (0:ℝ)..1, f x

section Monotone

variable {p : ℝ → ℝ}

/-- Each subinterval of the uniform partition of `[0,1]` into `N` pieces lies in `[0,1]`. -/
lemma uIcc_subset_unit {N k : ℕ} (hk : k < N) :
    Set.uIcc ((k : ℝ) / N) (((k : ℝ) + 1) / N) ⊆ Set.Icc (0 : ℝ) 1 := by
  have hN : (0 : ℝ) < N := by
    have : 0 < N := lt_of_le_of_lt (Nat.zero_le k) hk
    exact_mod_cast this
  rw [Set.uIcc_of_le (by gcongr; linarith)]
  apply Set.Icc_subset_Icc
  · positivity
  · rw [div_le_one hN]
    have : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
    linarith

/-- A monotone function is interval integrable on each piece of the uniform partition. -/
lemma intervalIntegrable_piece (hp : MonotoneOn p (Set.Icc (0:ℝ) 1)) {N k : ℕ} (hk : k < N) :
    IntervalIntegrable p MeasureTheory.volume ((k : ℝ) / N) (((k : ℝ) + 1) / N) :=
  MonotoneOn.intervalIntegrable (hp.mono (uIcc_subset_unit hk))

/-- The integral over `[0,1]` splits as the sum of the integrals over the pieces of the
uniform partition. -/
lemma sum_piece_integrals (hp : MonotoneOn p (Set.Icc (0:ℝ) 1)) {N : ℕ} (hN : 0 < N) :
    ∑ k ∈ Finset.range N, (∫ x in ((k : ℝ) / N)..(((k : ℝ) + 1) / N), p x)
      = ∫ x in (0:ℝ)..1, p x := by
  have h := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
    (a := fun k : ℕ => (k : ℝ) / N) (f := p) (n := N)
    (fun k hk => by simpa [Nat.cast_add] using intervalIntegrable_piece hp hk)
  have hN' : (N : ℝ) ≠ 0 := by positivity
  simpa [div_self hN'] using h

/-- Lower bound for the integral over one piece, by the left endpoint value. -/
lemma piece_lower (hp : MonotoneOn p (Set.Icc (0:ℝ) 1)) {N k : ℕ} (hk : k < N) :
    p ((k : ℝ) / N) / N ≤ ∫ x in ((k : ℝ) / N)..(((k : ℝ) + 1) / N), p x := by
  have hN : (0 : ℝ) < N := by
    have : 0 < N := lt_of_le_of_lt (Nat.zero_le k) hk
    exact_mod_cast this
  have hle : (k : ℝ) / N ≤ ((k : ℝ) + 1) / N := by gcongr; linarith
  have hmono := intervalIntegral.integral_mono_on (f := fun _ : ℝ => p ((k : ℝ) / N)) (g := p)
    hle intervalIntegrable_const (intervalIntegrable_piece hp hk) ?_
  · rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have hstep : ((k : ℝ) + 1) / N - (k : ℝ) / N = 1 / N := by field_simp; ring
    rw [hstep] at hmono
    calc p ((k : ℝ) / N) / N = 1 / N * p ((k : ℝ) / N) := by ring
      _ ≤ _ := hmono
  · intro x hx
    have hxmem : x ∈ Set.Icc (0:ℝ) 1 :=
      uIcc_subset_unit hk (by rw [Set.uIcc_of_le hle]; exact hx)
    have hkmem : (k : ℝ) / N ∈ Set.Icc (0:ℝ) 1 :=
      uIcc_subset_unit hk (by rw [Set.uIcc_of_le hle]; exact Set.left_mem_Icc.2 hle)
    exact hp hkmem hxmem hx.1

/-- Upper bound for the integral over one piece, by the right endpoint value. -/
lemma piece_upper (hp : MonotoneOn p (Set.Icc (0:ℝ) 1)) {N k : ℕ} (hk : k < N) :
    (∫ x in ((k : ℝ) / N)..(((k : ℝ) + 1) / N), p x) ≤ p (((k : ℝ) + 1) / N) / N := by
  have hN : (0 : ℝ) < N := by
    have : 0 < N := lt_of_le_of_lt (Nat.zero_le k) hk
    exact_mod_cast this
  have hle : (k : ℝ) / N ≤ ((k : ℝ) + 1) / N := by gcongr; linarith
  have hmono := intervalIntegral.integral_mono_on (f := p)
    (g := fun _ : ℝ => p (((k : ℝ) + 1) / N))
    hle (intervalIntegrable_piece hp hk) intervalIntegrable_const ?_
  · rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have hstep : ((k : ℝ) + 1) / N - (k : ℝ) / N = 1 / N := by field_simp; ring
    rw [hstep] at hmono
    calc (∫ x in ((k : ℝ) / N)..(((k : ℝ) + 1) / N), p x)
        ≤ 1 / N * p (((k : ℝ) + 1) / N) := hmono
      _ = p (((k : ℝ) + 1) / N) / N := by ring
  · intro x hx
    have hxmem : x ∈ Set.Icc (0:ℝ) 1 :=
      uIcc_subset_unit hk (by rw [Set.uIcc_of_le hle]; exact hx)
    have hkmem : ((k : ℝ) + 1) / N ∈ Set.Icc (0:ℝ) 1 :=
      uIcc_subset_unit hk (by rw [Set.uIcc_of_le hle]; exact Set.right_mem_Icc.2 hle)
    exact hp hxmem hkmem hx.2

/-- Left Riemann sums of a monotone function underestimate the integral. -/
lemma sum_div_le_integral (hp : MonotoneOn p (Set.Icc (0:ℝ) 1)) {N : ℕ} (hN : 0 < N) :
    total p N / N ≤ ∫ x in (0:ℝ)..1, p x := by
  rw [← sum_piece_integrals hp hN, total, Finset.sum_div]
  exact Finset.sum_le_sum fun k hk => piece_lower hp (Finset.mem_range.1 hk)

/-- Quantitative error bound for left Riemann sums of a monotone function. -/
lemma integral_sub_sum_div_le (hp : MonotoneOn p (Set.Icc (0:ℝ) 1)) {N : ℕ} (hN : 0 < N) :
    (∫ x in (0:ℝ)..1, p x) - total p N / N ≤ (p 1 - p 0) / N := by
  have hN' : (N : ℝ) ≠ 0 := by
    have : (0:ℝ) < N := by exact_mod_cast hN
    positivity
  have hupper : (∫ x in (0:ℝ)..1, p x)
      ≤ ∑ k ∈ Finset.range N, p (((k : ℝ) + 1) / N) / N := by
    rw [← sum_piece_integrals hp hN]
    exact Finset.sum_le_sum fun k hk => piece_upper hp (Finset.mem_range.1 hk)
  have htel : ∑ k ∈ Finset.range N,
      (p (((k : ℝ) + 1) / N) / N - p ((k : ℝ) / N) / N) = (p 1 - p 0) / N := by
    have := Finset.sum_range_sub (f := fun k : ℕ => p ((k : ℝ) / N) / N) N
    simp only [Nat.cast_add, Nat.cast_one] at this
    rw [this, div_self hN']
    simp [sub_div]
  have hsum : total p N / N = ∑ k ∈ Finset.range N, p ((k : ℝ) / N) / N := by
    rw [total, Finset.sum_div]
  rw [hsum, ← htel, Finset.sum_sub_distrib]
  linarith [hupper]

/-- Left Riemann sums of a monotone function converge to the integral. -/
lemma tendsto_sum_div_monotone (hp : MonotoneOn p (Set.Icc (0:ℝ) 1)) :
    Tendsto (fun N : ℕ => total p N / N) atTop (nhds (∫ x in (0:ℝ)..1, p x)) := by
  have hbound : ∀ᶠ N : ℕ in atTop,
      |total p N / N - ∫ x in (0:ℝ)..1, p x| ≤ |p 1 - p 0| / N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have h1 := sum_div_le_integral hp hN
    have h2 := integral_sub_sum_div_le hp hN
    have hN' : (0:ℝ) < N := by exact_mod_cast hN
    rw [abs_le]
    constructor
    · have : (p 1 - p 0) / N ≤ |p 1 - p 0| / N := by
        gcongr
        exact le_abs_self _
      linarith
    · have : (0:ℝ) ≤ |p 1 - p 0| / N := by positivity
      linarith
  have hzero : Tendsto (fun N : ℕ => |p 1 - p 0| / N) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => dist_nonneg) ?_ hzero
  filter_upwards [hbound] with N hN using by rwa [Real.dist_eq]

end Monotone

/-- **Equidistribution / bounded-variation reduction.**
For a function `f` of bounded variation on `[0,1]` whose mean value over `[0,1]` is nonzero,
the total `∑_{k<N} f (k/N)` of the values of `f` over the `N` equidistributed sample points
is asymptotic to the main term `N * ∫₀¹ f`, i.e. their ratio tends to `1`.

This is the unconditional form: no equidistribution hypothesis is assumed, it is proved here
for the uniform sample points via the bounded-variation (monotone difference) reduction. -/
theorem total_over_main_tendsto {f : ℝ → ℝ}
    (hf : BoundedVariationOn f (Set.Icc (0:ℝ) 1))
    (hI : (∫ x in (0:ℝ)..1, f x) ≠ 0) :
    Tendsto (fun N : ℕ => total f N / main f N) atTop (nhds 1) := by
  obtain ⟨p, q, hp, hq, hpq⟩ := hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have hpi : IntervalIntegrable p MeasureTheory.volume 0 1 :=
    MonotoneOn.intervalIntegrable (by rwa [Set.uIcc_of_le (zero_le_one)])
  have hqi : IntervalIntegrable q MeasureTheory.volume 0 1 :=
    MonotoneOn.intervalIntegrable (by rwa [Set.uIcc_of_le (zero_le_one)])
  have hfx : ∀ x, f x = p x - q x := fun x => by rw [hpq]; simp
  have hIf : (∫ x in (0:ℝ)..1, f x)
      = (∫ x in (0:ℝ)..1, p x) - ∫ x in (0:ℝ)..1, q x := by
    rw [← intervalIntegral.integral_sub hpi hqi]
    exact intervalIntegral.integral_congr (fun x _ => hfx x)
  have htotal : ∀ N : ℕ, total f N = total p N - total q N := by
    intro N
    simp only [total, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact hfx _
  have hmain : Tendsto (fun N : ℕ => total f N / N) atTop
      (nhds (∫ x in (0:ℝ)..1, f x)) := by
    have := (tendsto_sum_div_monotone hp).sub (tendsto_sum_div_monotone hq)
    rw [hIf]
    refine this.congr fun N => ?_
    rw [htotal N, sub_div]
  have hfinal : Tendsto (fun N : ℕ => (total f N / N) / (∫ x in (0:ℝ)..1, f x)) atTop
      (nhds 1) := by
    have := hmain.div_const (∫ x in (0:ℝ)..1, f x)
    rwa [div_self hI] at this
  refine hfinal.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN' : (N : ℝ) ≠ 0 := by
    have : (0:ℝ) < N := by exact_mod_cast hN
    positivity
  rw [main, div_div, mul_comm]

/-- A function monotone on `[0,1]` has bounded variation there. -/
lemma monotoneOn_unit_boundedVariationOn {f : ℝ → ℝ}
    (hf : MonotoneOn f (Set.Icc (0:ℝ) 1)) : BoundedVariationOn f (Set.Icc (0:ℝ) 1) := by
  have h := hf.eVariationOn_le (Set.left_mem_Icc.2 zero_le_one)
    (Set.right_mem_Icc.2 zero_le_one)
  rw [Set.inter_self] at h
  exact (h.trans_lt ENNReal.ofReal_lt_top).ne

/-- Sanity check: the hypotheses of `total_over_main_tendsto` are satisfiable, e.g. by the
identity function on `[0,1]`. -/
example : Tendsto (fun N : ℕ => total (fun x => x) N / main (fun x => x) N) atTop (nhds 1) := by
  refine total_over_main_tendsto (monotoneOn_unit_boundedVariationOn ?_) ?_
  · exact fun a _ b _ hab => hab
  · rw [integral_id]
    norm_num

end EquidistributionBVReduction
end Brockian

