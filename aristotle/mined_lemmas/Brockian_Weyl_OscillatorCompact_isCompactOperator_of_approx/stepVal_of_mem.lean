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

theorem stepVal_of_mem (c : ℕ → ℂ) {Rr hh : ℝ} (hh0 : 0 < hh) {n k : ℕ} (hk : k < n)
    {x : ℝ} (hx : x ∈ cellSet Rr hh k) : stepVal c Rr hh n x = c k := by
  rw [stepVal, Finset.sum_eq_single k]
  · rw [Set.indicator_of_mem hx]
  · intro j _ hjk
    exact Set.indicator_of_notMem
      (fun hxj => (cells_disjoint Rr hh hh0 hjk).le_bot ⟨hxj, hx⟩) _
  · intro hkn; exact absurd (Finset.mem_range.mpr hk) hkn

