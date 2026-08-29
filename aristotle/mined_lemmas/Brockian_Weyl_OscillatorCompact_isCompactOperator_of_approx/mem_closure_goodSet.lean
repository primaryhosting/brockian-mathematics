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

theorem mem_closure_goodSet (u : (harmonicOscillatorPMap.closure).domain)
    (h1 : ‖(u : L2R)‖ ≤ 1) (h2 : ‖harmonicOscillatorPMap.closure u‖ ≤ 1) :
    (u : L2R) ∈ closure (goodSet 2) := by
  obtain ⟨g, hg1, hg2⟩ := exists_seq_schwartz_tendsto u
  -- the norms converge
  have hnorm : Tendsto (fun n => ‖schwartzToL2 (g n)‖) atTop (𝓝 ‖(u : L2R)‖) :=
    (continuous_norm.tendsto _).comp hg1
  -- the energies converge
  have hinner : Tendsto (fun n => inner ℂ (oscillatorCoreMap (g n)) (schwartzToL2 (g n)))
      atTop (𝓝 (inner ℂ (harmonicOscillatorPMap.closure u) ((u : L2R)))) :=
    (continuous_inner (𝕜 := ℂ)).continuousAt.tendsto.comp (hg2.prodMk_nhds hg1)
  have henergy : Tendsto (fun n => energy (g n)) atTop
      (𝓝 (inner ℂ (harmonicOscillatorPMap.closure u) ((u : L2R))).re) := by
    have h := (Complex.continuous_re.tendsto _).comp hinner
    simp only [Function.comp_def, inner_oscillatorCoreMap_self, Complex.ofReal_re] at h
    exact h
  -- the limits are at most one
  have hlim2 : (inner ℂ (harmonicOscillatorPMap.closure u) ((u : L2R))).re ≤ 1 := by
    have hle : ‖inner ℂ (harmonicOscillatorPMap.closure u) ((u : L2R))‖
        ≤ ‖harmonicOscillatorPMap.closure u‖ * ‖(u : L2R)‖ := norm_inner_le_norm _ _
    have h3 : ‖harmonicOscillatorPMap.closure u‖ * ‖(u : L2R)‖ ≤ 1 := by
      have := norm_nonneg (u : L2R)
      have := norm_nonneg (harmonicOscillatorPMap.closure u)
      nlinarith
    have h4 := Complex.re_le_norm (inner ℂ (harmonicOscillatorPMap.closure u) ((u : L2R)))
    linarith
  -- eventually the Schwartz approximants lie in the good set
  have hev : ∀ᶠ n in atTop, schwartzToL2 (g n) ∈ goodSet 2 := by
    have e1 : ∀ᶠ n in atTop, ‖schwartzToL2 (g n)‖ < 2 :=
      hnorm.eventually_lt_const (by linarith)
    have e2 : ∀ᶠ n in atTop, energy (g n) < 2 :=
      henergy.eventually_lt_const (by linarith)
    filter_upwards [e1, e2] with n hn1 hn2
    exact ⟨g n, rfl, hn1.le, hn2.le⟩
  exact mem_closure_of_tendsto hg1 hev

/-- The unit-shift resolvents map the closed unit ball into the closure of the
good set. -/
