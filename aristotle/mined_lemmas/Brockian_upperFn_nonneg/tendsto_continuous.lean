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

import Brockian.WeylEquidistribution

/-!
# Equidistribution: reduction of a configuration count to its main term

Fix an irrational number `a`, a point `c` on the circle `ℝ/ℤ` and a radius `r` with
`0 < r < 1/2`.  Call `n` *admissible* if the orbit point `n • a` lies within distance `r` of `c`
on `ℝ/ℤ`.  `configCount a c r N` counts the admissible `n < N`, and the expected main term is
`mainTerm r N = 2 * r * N` (the measure of the arc times the number of trials).

The main result `configCount_over_main_tendsto` states that the ratio of the count to the main
term tends to `1`.

The analytic input is Weyl's equidistribution theorem for continuous test functions, proved in
`Brockian.WeylEquidistribution`; the passage from continuous test functions to the (bounded
variation, indeed indicator) test function of an arc is done here by sandwiching the indicator
between two explicit continuous, piecewise-linear functions.
-/

open MeasureTheory Filter Topology Metric
open scoped BigOperators

namespace Brockian
namespace EquidistributionBVReduction

open Brockian.Weyl

noncomputable section

open scoped Classical in
/-- The number of `n < N` for which the orbit point `n • a` lies within distance `r` of `c`
on the circle `ℝ/ℤ`. -/

theorem tendsto_continuous (a : ℝ) (ha : Irrational a) (f : C(Circ, ℂ)) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (pt a n))
      atTop (𝓝 (∫ x : Circ, f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hg, hfg⟩ :
      ∃ g ∈ span ℂ (Set.range (fourier : ℤ → C(Circ, ℂ))), ‖f - g‖ < ε / 3 := by
    have h : f ∈ (span ℂ (Set.range (fourier : ℤ → C(Circ, ℂ)))).topologicalClosure := by
      rw [span_fourier_closure_eq_top]; trivial
    have h2 : f ∈ closure ((span ℂ (Set.range (fourier : ℤ → C(Circ, ℂ)))) : Set _) := h
    rw [Metric.mem_closure_iff] at h2
    obtain ⟨g, hg, hd⟩ := h2 (ε / 3) (by linarith)
    exact ⟨g, hg, by rwa [← dist_eq_norm]⟩
  have hgt := tendsto_of_mem_span a ha g hg
  rw [Metric.tendsto_atTop] at hgt
  obtain ⟨N₀, hN₀⟩ := hgt (ε / 3) (by linarith)
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNN : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hsum : ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (pt a n)
      - (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, g (pt a n)‖ ≤ ‖f - g‖ := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_inv, Complex.norm_natCast]
    have h1 : ‖∑ n ∈ Finset.range N, (f (pt a n) - g (pt a n))‖ ≤ N * ‖f - g‖ := by
      calc ‖∑ n ∈ Finset.range N, (f (pt a n) - g (pt a n))‖
          ≤ ∑ n ∈ Finset.range N, ‖f (pt a n) - g (pt a n)‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.range N, ‖f - g‖ := by
            refine Finset.sum_le_sum fun n _ => ?_
            simpa using (f - g).norm_coe_le_norm (pt a n)
        _ = N * ‖f - g‖ := by simp [Finset.sum_const]
    rw [inv_mul_le_iff₀ hN0]
    exact h1
  have hint : ‖(∫ x : Circ, g x) - ∫ x : Circ, f x‖ ≤ ‖f - g‖ := by
    rw [← integral_sub (integrable_continuous g) (integrable_continuous f)]
    have hpt : ∀ x, ‖g x - f x‖ ≤ ‖f - g‖ := by
      intro x
      rw [norm_sub_rev]
      simpa using (f - g).norm_coe_le_norm x
    calc ‖∫ x : Circ, (g x - f x)‖
        ≤ ‖f - g‖ * (volume (Set.univ : Set Circ)).toReal :=
          norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hpt)
      _ = ‖f - g‖ := by simp
  have hmid := hN₀ N hNN
  rw [dist_eq_norm] at hmid ⊢
  calc ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (pt a n) - ∫ x : Circ, f x‖
      ≤ ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (pt a n)
            - (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, g (pt a n)‖
        + ‖(N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, g (pt a n) - ∫ x : Circ, g x‖
        + ‖(∫ x : Circ, g x) - ∫ x : Circ, f x‖ := by
        have := norm_add₃_le
          (a := (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (pt a n)
                - (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, g (pt a n))
          (b := (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, g (pt a n) - ∫ x : Circ, g x)
          (c := (∫ x : Circ, g x) - ∫ x : Circ, f x)
        simpa using this
    _ < ε := by linarith

/-- **Weyl's equidistribution theorem** for continuous real-valued test functions. -/
