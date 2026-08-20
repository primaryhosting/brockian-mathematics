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
# Weyl's equidistribution theorem for irrational rotations

For an irrational number `a`, the fractional parts `{n * a}` are equidistributed in `[0,1)`:
for every subinterval `[u, v) ⊆ [0,1]` the proportion of `n < N` with `Int.fract (n * a) ∈ [u, v)`
tends to `v - u`.

The proof follows Weyl's method:

* `WeylSumsVanish a` is the statement that all non-trivial exponential (Weyl) sums along the
  orbit have vanishing averages;
* `tendsto_orbitAvg_of_weylSumsVanish` is the *conditional* statement that `WeylSumsVanish a`
  implies convergence of Birkhoff averages of continuous functions to their integral;
* `weylSumsVanish_of_irrational` *discharges* that hypothesis for irrational `a` (geometric
  series estimate), making the result unconditional;
* `equidistribution_of_asymptotic_exists` is the final unconditional interval version.
-/

namespace Brockian.Equidistribution

open Filter Topology MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- Birkhoff / empirical average of a complex-valued function over the first `N` points of the
orbit of `0` under the rotation by `a` on the circle `ℝ / ℤ`. -/

theorem equidistribution_of_asymptotic_exists {a : ℝ} (ha : Irrational a) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    Tendsto (fun N : ℕ =>
        (((Finset.range N).filter fun n : ℕ => Int.fract ((n : ℝ) * a) ∈ Ico u v).card : ℝ) / N)
      atTop (𝓝 (v - u)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := ε / 6 with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨g₁, hg₁0, hg₁1, hg₁supp, hg₁int⟩ := exists_tent hu hv hδ
  obtain ⟨ga, hga0, hga1, hgasupp, hgaint⟩ := exists_tent le_rfl (huv.trans hv) hδ
  obtain ⟨gb, hgb0, hgb1, hgbsupp, hgbint⟩ := exists_tent (hu.trans huv) le_rfl hδ
  set g₂ : C(AddCircle (1 : ℝ), ℝ) := 1 - ga - gb with hg₂def
  -- the integral of the upper approximation
  have hint2 : (∫ x, g₂ x ∂AddCircle.haarAddCircle)
      = 1 - (∫ x, ga x ∂AddCircle.haarAddCircle) - ∫ x, gb x ∂AddCircle.haarAddCircle := by
    have hIa := integrable_of_continuousMap ga
    have hIb := integrable_of_continuousMap gb
    have h1 : (∫ _x : AddCircle (1 : ℝ), (1 : ℝ) ∂AddCircle.haarAddCircle) = 1 := by simp
    have e : ∀ x, g₂ x = 1 - ga x - gb x := by
      intro x; simp [hg₂def]
    have h2 : (∫ x, ((1 : ℝ) - ga x - gb x) ∂AddCircle.haarAddCircle)
        = (∫ x, ((1 : ℝ) - ga x) ∂AddCircle.haarAddCircle)
          - ∫ x, gb x ∂AddCircle.haarAddCircle :=
      integral_sub (f := fun x => (1 : ℝ) - ga x) (g := fun x => gb x)
        ((integrable_const (1 : ℝ)).sub hIa) hIb
    have h3 : (∫ x, ((1 : ℝ) - ga x) ∂AddCircle.haarAddCircle)
        = 1 - ∫ x, ga x ∂AddCircle.haarAddCircle := by
      rw [integral_sub (f := fun _ => (1 : ℝ)) (g := fun x => ga x) (integrable_const (1 : ℝ)) hIa,
        h1]
    simp only [e]
    rw [h2, h3]
  have hint2' : (∫ x, g₂ x ∂AddCircle.haarAddCircle) ≤ v - u + 4 * δ := by
    rw [hint2]; linarith
  -- comparison of the Birkhoff averages with the counting density
  have hlow : ∀ N : ℕ, orbitAvgR a g₁ N
      ≤ (((Finset.range N).filter fun n : ℕ => Int.fract ((n : ℝ) * a) ∈ Ico u v).card : ℝ) / N := by
    intro N
    rw [density_eq_avg_indicator, orbitAvgR]
    have hpt : ∀ n ∈ Finset.range N, g₁ ((n * a : ℝ) : AddCircle (1 : ℝ))
        ≤ (if Int.fract ((n : ℝ) * a) ∈ Ico u v then (1 : ℝ) else 0) := by
      intro n _
      by_cases hmem : Int.fract ((n : ℝ) * a) ∈ Ico u v
      · rw [if_pos hmem]; exact hg₁1 _
      · have hnot : Int.fract ((n : ℝ) * a) ∉ Ioo u v := fun hx => hmem ⟨hx.1.le, hx.2⟩
        rw [if_neg hmem, hg₁supp _ hnot]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpt) (by positivity)
  have hhigh : ∀ N : ℕ,
      (((Finset.range N).filter fun n : ℕ => Int.fract ((n : ℝ) * a) ∈ Ico u v).card : ℝ) / N
        ≤ orbitAvgR a g₂ N := by
    intro N
    rw [density_eq_avg_indicator, orbitAvgR]
    have hpt : ∀ n ∈ Finset.range N,
        (if Int.fract ((n : ℝ) * a) ∈ Ico u v then (1 : ℝ) else 0)
          ≤ g₂ ((n * a : ℝ) : AddCircle (1 : ℝ)) := by
      intro n _
      have hfr := Int.fract_nonneg ((n : ℝ) * a)
      have hfr1 := Int.fract_lt_one ((n : ℝ) * a)
      by_cases hmem : Int.fract ((n : ℝ) * a) ∈ Ico u v
      · have hna : Int.fract ((n : ℝ) * a) ∉ Ioo (0 : ℝ) u := fun hx =>
          absurd hmem.1 (not_le.mpr hx.2)
        have hnb : Int.fract ((n : ℝ) * a) ∉ Ioo v 1 := fun hx =>
          absurd hmem.2 (not_lt.mpr hx.1.le)
        rw [if_pos hmem, hg₂def]
        simp only [ContinuousMap.sub_apply, ContinuousMap.one_apply]
        rw [hgasupp _ hna, hgbsupp _ hnb]
        norm_num
      · have hle : ga ((n * a : ℝ) : AddCircle (1 : ℝ)) + gb ((n * a : ℝ) : AddCircle (1 : ℝ))
            ≤ 1 := by
          by_cases hx : Int.fract ((n : ℝ) * a) ∈ Ioo (0 : ℝ) u
          · have hnb : Int.fract ((n : ℝ) * a) ∉ Ioo v 1 := fun hy =>
              absurd (hx.2.trans_le (huv.trans hy.1.le)) (lt_irrefl _)
            have := hga1 ((n * a : ℝ) : AddCircle (1 : ℝ))
            rw [hgbsupp _ hnb]
            linarith
          · have := hgb1 ((n * a : ℝ) : AddCircle (1 : ℝ))
            rw [hgasupp _ hx]
            linarith
        simp only [hmem, if_false, hg₂def, ContinuousMap.sub_apply, ContinuousMap.one_apply]
        linarith
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpt) (by positivity)
  -- pass to the limit
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp (tendsto_orbitAvgR ha g₁) δ hδ
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp (tendsto_orbitAvgR ha g₂) δ hδ
  refine ⟨max N₁ N₂, fun N hN => ?_⟩
  have h1 := hN₁ N (le_trans (le_max_left _ _) hN)
  have h2 := hN₂ N (le_trans (le_max_right _ _) hN)
  rw [Real.dist_eq, abs_lt] at h1 h2
  rw [Real.dist_eq, abs_lt]
  have hl := hlow N
  have hh := hhigh N
  constructor <;> [linarith; linarith]

end

end Brockian.Equidistribution

