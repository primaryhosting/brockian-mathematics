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

theorem isClosable_of_isSymmetric {T : H →ₗ.[ℂ] H} (hsym : IsSymmetric T)
    (hd : Dense (T.domain : Set H)) : T.IsClosable :=
  LinearPMap.isClosable_iff_exists_closed_extension.mpr
    ⟨T.adjoint, LinearPMap.adjoint_isClosed hd, le_adjoint_of_isSymmetric hsym hd⟩

omit [CompleteSpace H] in
/-- A closed operator equals its own closure. -/
