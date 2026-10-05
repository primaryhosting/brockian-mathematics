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

theorem exists_approx_of_mem_closure {C ε : ℝ} (hε : 0 < ε)
    {V : Submodule ℂ L2R} (hV : ∀ u ∈ goodSet C, ∃ v ∈ V, ‖u - v‖ ≤ ε)
    {u : L2R} (hu : u ∈ closure (goodSet C)) : ∃ v ∈ V, ‖u - v‖ ≤ 2 * ε := by
  obtain ⟨w, hw, hdist⟩ := Metric.mem_closure_iff.mp hu ε hε
  obtain ⟨v, hvV, hv⟩ := hV w hw
  refine ⟨v, hvV, ?_⟩
  have h1 : ‖u - w‖ ≤ ε := by
    rw [← dist_eq_norm]; exact hdist.le
  calc ‖u - v‖ = ‖(u - w) + (w - v)‖ := by congr 1; abel
    _ ≤ ‖u - w‖ + ‖w - v‖ := norm_add_le _ _
    _ ≤ ε + ε := add_le_add h1 hv
    _ = 2 * ε := by ring

/-! ### The resolvent maps the unit ball into the good set -/

/-- Every element of the oscillator core domain comes from a Schwartz
function. -/
