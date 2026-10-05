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

theorem closure_eq_self_of_isClosed {T : H →ₗ.[ℂ] H} (h : T.IsClosed) :
    T.closure = T := by
  refine LinearPMap.eq_of_eq_graph ?_
  rw [← h.isClosable.graph_closure_eq_closure_graph]
  exact (h.submodule_topologicalClosure_eq)

/-- The closure of a densely defined symmetric operator is contained in the
adjoint. -/
