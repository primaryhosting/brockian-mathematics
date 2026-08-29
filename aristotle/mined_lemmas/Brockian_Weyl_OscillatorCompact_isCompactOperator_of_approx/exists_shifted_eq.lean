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

theorem exists_shifted_eq {T : H →ₗ.[ℂ] H} (hsym : IsSymmetric T)
    (hd : Dense (T.domain : Set H)) {z : ℂ}
    (hz : |z.im| = 1) (hdef : deficiencySpace T ((starRingEnd ℂ) z) = ⊥) (y : H) :
    ∃ v : T.closure.domain, T.closure v - z • (v : H) = y := by
  have h := shiftedRange_closure_eq_top hsym hd hz hdef
  have : y ∈ shiftedRange T.closure z := by rw [h]; trivial
  exact (mem_shiftedRange_iff T.closure z y).mp this

/-! ### The bounded inverse -/

/-- The bounded inverse of `S - z` for a symmetric `S`, given surjectivity. -/
