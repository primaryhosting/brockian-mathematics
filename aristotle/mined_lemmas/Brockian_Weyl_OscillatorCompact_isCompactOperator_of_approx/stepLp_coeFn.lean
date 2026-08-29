/-
  CompactCriterion.lean — an abstract compactness criterion: an operator whose
  unit-ball image is uniformly approximable by finite-dimensional subspaces is
  a compact operator.
-/
import Mathlib

open Metric Filter

namespace Brockian.Weyl.OscillatorCompact

/-- An operator whose closed-unit-ball image is uniformly approximable by
finite-dimensional subspaces is a compact operator. -/

theorem stepLp_coeFn (c : ℕ → ℂ) (Rr hh : ℝ) (n : ℕ) :
    ⇑(stepLp c Rr hh n) =ᵐ[volume] stepVal c Rr hh n := by
  have hj : ∀ᵐ x : ℝ, ∀ j : ℕ,
      (c j • cellLp Rr hh j) x = Set.indicator (cellSet Rr hh j) (fun _ => c j) x := by
    rw [ae_all_iff]
    intro j
    filter_upwards [Lp.coeFn_smul (c j) (cellLp Rr hh j),
      indicatorConstLp_coeFn (p := 2) (μ := (volume : Measure ℝ))
        (hs := measurableSet_Ioc (a := -Rr + j * hh) (b := -Rr + (j + 1) * hh))
        (hμs := measure_Ioc_lt_top.ne) (c := (1 : ℂ))] with x h1 h2
    rw [h1]
    simp only [Pi.smul_apply, cellLp]
    rw [h2]
    by_cases hx : x ∈ cellSet Rr hh j
    · rw [Set.indicator_of_mem hx,
        Set.indicator_of_mem (s := Set.Ioc (-Rr + j * hh) (-Rr + (j + 1) * hh)) hx]
      simp
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (s := Set.Ioc (-Rr + j * hh) (-Rr + (j + 1) * hh)) hx]
      simp
  filter_upwards [coeFn_finset_sum (Finset.range n) (fun j => c j • cellLp Rr hh j), hj]
    with x h1 h2
  rw [stepLp, h1, stepVal]
  exact Finset.sum_congr rfl fun j _ => h2 j

/-! ### `L²` norms as integrals, and the integrability facts we need -/

