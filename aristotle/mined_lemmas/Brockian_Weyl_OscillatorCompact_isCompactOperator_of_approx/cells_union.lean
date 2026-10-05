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

theorem cells_union (Rr hh : ℝ) (hh0 : 0 ≤ hh) : ∀ n : ℕ,
    (⋃ j ∈ Finset.range n, cellSet Rr hh j) = Set.Ioc (-Rr) (-Rr + n * hh) := by
  intro n
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.range_add_one, Finset.set_biUnion_insert, ih, Set.union_comm, cellSet]
      rw [Set.Ioc_union_Ioc_eq_Ioc (by nlinarith [Nat.cast_nonneg (α := ℝ) m])
        (by nlinarith)]
      congr 1
      push_cast
      ring

/-- The pointwise step function with value `c j` on the `j`-th cell. -/
