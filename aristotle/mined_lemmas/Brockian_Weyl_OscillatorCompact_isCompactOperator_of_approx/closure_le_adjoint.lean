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

theorem closure_le_adjoint {T : H →ₗ.[ℂ] H} (hsym : IsSymmetric T)
    (hd : Dense (T.domain : Set H)) : T.closure ≤ T.adjoint := by
  have hcl : (T.adjoint).IsClosed := LinearPMap.adjoint_isClosed hd
  have h := hcl.isClosable.closure_mono (le_adjoint_of_isSymmetric hsym hd)
  rwa [closure_eq_self_of_isClosed hcl] at h

omit [CompleteSpace H] in
/-- Every element of the domain of the closure is a graph limit of elements of
the domain. -/
