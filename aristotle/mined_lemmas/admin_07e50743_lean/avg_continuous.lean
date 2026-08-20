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

/-
Weyl's criterion for equidistribution modulo one, and its application to the
sequence `n ↦ n • α` for irrational `α`.
-/
import Mathlib

open Filter MeasureTheory Metric Set Submodule
open scoped Topology Real

namespace Brockian.Equidistribution

noncomputable section

/-! ## Definitions -/

/-- A sequence `u : ℕ → ℝ` is *equidistributed modulo one* if for every subinterval
`[a, b) ⊆ [0, 1]` the proportion of the first `N` terms whose fractional part lies in `[a, b)`
tends to `b - a`. -/

lemma avg_continuous (hweyl : ∀ h : ℤ, h ≠ 0 → Tendsto (weylSum u h) atTop (𝓝 0))
    (f : C(UnitAddCircle, ℂ)) :
    Tendsto (avg u f) atTop (𝓝 (∫ z : UnitAddCircle, f z)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η := ε / 4 with hη
  have hηpos : 0 < η := by positivity
  have hmem : f ∈ closure ((span ℂ (range (fourier (T := 1)))) : Set C(UnitAddCircle, ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
    trivial
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.1 hmem η hηpos
  have hbound : ∀ z : UnitAddCircle, ‖f z - g z‖ ≤ η := by
    intro z
    have h1 : ‖(f - g) z‖ ≤ ‖f - g‖ := ContinuousMap.norm_coe_le_norm (f - g) z
    have h2 : ‖f - g‖ < η := by rwa [dist_eq_norm] at hfg
    simpa [ContinuousMap.sub_apply] using h1.trans h2.le
  have havg : ∀ N : ℕ, 0 < N → dist (avg u f N) (avg u g N) ≤ η := by
    intro N hN
    have hsum : ‖∑ k ∈ Finset.range N,
        (f ((u k : ℝ) : UnitAddCircle) - g ((u k : ℝ) : UnitAddCircle))‖ ≤ N * η := by
      refine le_trans (norm_sum_le _ _) ?_
      calc ∑ k ∈ Finset.range N, ‖f ((u k : ℝ) : UnitAddCircle) - g ((u k : ℝ) : UnitAddCircle)‖
          ≤ ∑ _k ∈ Finset.range N, η := Finset.sum_le_sum fun k _ => hbound _
        _ = N * η := by simp
    have hrw : avg u f N - avg u g N = (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N,
        (f ((u k : ℝ) : UnitAddCircle) - g ((u k : ℝ) : UnitAddCircle)) := by
      simp only [avg, Finset.sum_sub_distrib, mul_sub]
    rw [dist_eq_norm, hrw, norm_mul, norm_inv, Complex.norm_natCast]
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    calc (N : ℝ)⁻¹ * ‖∑ k ∈ Finset.range N,
            (f ((u k : ℝ) : UnitAddCircle) - g ((u k : ℝ) : UnitAddCircle))‖
        ≤ (N : ℝ)⁻¹ * (N * η) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = η := by field_simp
  have hint : dist (∫ z : UnitAddCircle, f z) (∫ z : UnitAddCircle, g z) ≤ η := by
    rw [dist_eq_norm, ← integral_sub (integrable_of_continuous f) (integrable_of_continuous g)]
    have := norm_integral_le_of_norm_le_const (μ := (volume : Measure UnitAddCircle))
      (f := fun z => f z - g z) (C := η) (Filter.Eventually.of_forall hbound)
    simpa [measureReal_def, UnitAddCircle.measure_univ] using this
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 (avg_span u hweyl g hg) η hηpos
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have h1 : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have h2 : 0 < N := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hN)
  calc dist (avg u f N) (∫ z : UnitAddCircle, f z)
      ≤ dist (avg u f N) (avg u g N) + dist (avg u g N) (∫ z : UnitAddCircle, g z)
        + dist (∫ z : UnitAddCircle, g z) (∫ z : UnitAddCircle, f z) := dist_triangle4 _ _ _ _
    _ ≤ η + η + η := by
        gcongr
        · exact havg N h2
        · exact (hN₀ N h1).le
        · rw [dist_comm]; exact hint
    _ < ε := by rw [hη]; linarith

