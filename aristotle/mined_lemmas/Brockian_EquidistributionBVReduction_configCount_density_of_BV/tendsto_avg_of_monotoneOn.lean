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
