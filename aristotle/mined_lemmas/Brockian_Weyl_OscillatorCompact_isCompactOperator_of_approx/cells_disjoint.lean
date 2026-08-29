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

theorem cells_disjoint (Rr hh : ℝ) (hh0 : 0 < hh) :
    Pairwise (Function.onFun Disjoint (cellSet Rr hh)) := by
  have key : ∀ i j : ℕ, i < j → Disjoint (cellSet Rr hh i) (cellSet Rr hh j) := by
    intro i j hij
    apply Set.Ioc_disjoint_Ioc.mpr
    have hcast : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    have h1 : -Rr + ((i : ℝ) + 1) * hh ≤ -Rr + j * hh := by nlinarith
    calc min (-Rr + ((i : ℝ) + 1) * hh) (-Rr + ((j : ℝ) + 1) * hh)
        ≤ -Rr + ((i : ℝ) + 1) * hh := min_le_left _ _
      _ ≤ -Rr + (j : ℝ) * hh := h1
      _ ≤ max (-Rr + (i : ℝ) * hh) (-Rr + (j : ℝ) * hh) := le_max_right _ _
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

