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

theorem exists_finiteDimensional_approx (C : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Submodule ℂ L2R, FiniteDimensional ℂ V ∧
      ∀ u ∈ goodSet C, ∃ v ∈ V, ‖u - v‖ ≤ ε := by
  classical
  rcases lt_or_ge C 0 with hC | hC
  · refine ⟨⊥, inferInstance, ?_⟩
    rintro u ⟨g, -, -, hen⟩
    exact absurd (le_trans (energy_nonneg g) hen) (not_le.mpr hC)
  -- the geometric parameters
  set Rr : ℝ := 1 + 2 * C / ε ^ 2 with hRrdef
  have hRr1 : (1:ℝ) ≤ Rr := by
    have : 0 ≤ 2 * C / ε ^ 2 := by positivity
    linarith
  have hRr0 : 0 < Rr := by linarith
  have hRrbd : 2 * C ≤ ε ^ 2 * Rr ^ 2 := by
    have h1 : ε ^ 2 * (2 * C / ε ^ 2) = 2 * C := by field_simp
    have h2 : Rr ≤ Rr ^ 2 := by nlinarith
    nlinarith [sq_nonneg ε, hε]
  set δ : ℝ := ε / (2 * (C + 1)) with hδdef
  have hδ0 : 0 < δ := by
    apply div_pos hε
    linarith
  set n : ℕ := ⌈2 * Rr / δ⌉₊ + 1 with hndef
  have hn0 : 0 < n := Nat.succ_pos _
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  set hh : ℝ := 2 * Rr / n with hhdef
  have hh0 : 0 < hh := by
    apply div_pos (by linarith) hnR
  have hhδ : hh ≤ δ := by
    have hceil : 2 * Rr / δ ≤ (n : ℝ) := by
      have := Nat.le_ceil (2 * Rr / δ)
      push_cast [hndef]
      linarith
    rw [hhdef, div_le_iff₀ hnR]
    rw [div_le_iff₀ hδ0] at hceil
    linarith
  have hnhh : -Rr + n * hh = Rr := by
    have hnh : (n : ℝ) * hh = 2 * Rr := by
      rw [hhdef]; field_simp
    linarith
  -- the finite-dimensional space of step functions
  refine ⟨Submodule.span ℂ ↑((Finset.range n).image (cellLp Rr hh)),
    FiniteDimensional.span_of_finite ℂ (Finset.finite_toSet _), ?_⟩
  rintro u ⟨g, rfl, -, hen⟩
  refine ⟨stepLp (fun j => g (-Rr + (j + 1) * hh)) Rr hh n, ?_, ?_⟩
  · refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span (by simpa using ⟨j, Finset.mem_range.mp hj, rfl⟩)
  · -- the estimate
    have hd0 : 0 ≤ ∫ x : ℝ, ‖deriv (g : ℝ → ℂ) x‖ ^ 2 :=
      integral_nonneg fun _ => by positivity
    have hq0 : 0 ≤ ∫ x : ℝ, x ^ 2 * ‖g x‖ ^ 2 := integral_nonneg fun _ => by positivity
    have hdC : (∫ x : ℝ, ‖deriv (g : ℝ → ℂ) x‖ ^ 2) ≤ C := by
      rw [energy] at hen; linarith
    have hqC : (∫ x : ℝ, x ^ 2 * ‖g x‖ ^ 2) ≤ C := by
      rw [energy] at hen; linarith
    have hmain := approx_estimate g hRr0 hh0 hnhh
    -- tail bound
    have htail : (∫ x : ℝ, x ^ 2 * ‖g x‖ ^ 2) / Rr ^ 2 ≤ ε ^ 2 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hqC, hRrbd, sq_nonneg Rr]
    -- cell bound
    have hcellb : hh ^ 2 * (∫ x : ℝ, ‖deriv (g : ℝ → ℂ) x‖ ^ 2) ≤ ε ^ 2 / 2 := by
      have hδ2 : δ ^ 2 * C ≤ ε ^ 2 / 2 := by
        rw [hδdef, div_pow, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        have hk : C * 2 ≤ (2 * (C + 1)) ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hk (sq_nonneg ε)]
      have hh2 : hh ^ 2 ≤ δ ^ 2 := by nlinarith [hh0.le, hδ0.le]
      nlinarith [hd0, hdC, sq_nonneg hh, hh0.le]
    have hfin : ‖schwartzToL2 g - stepLp (fun j => g (-Rr + (j + 1) * hh)) Rr hh n‖ ^ 2
        ≤ ε ^ 2 := by linarith
    nlinarith [norm_nonneg (schwartzToL2 g -
      stepLp (fun j => g (-Rr + (j + 1) * hh)) Rr hh n), hε, hfin]

end Brockian.Weyl.OscillatorCompact

