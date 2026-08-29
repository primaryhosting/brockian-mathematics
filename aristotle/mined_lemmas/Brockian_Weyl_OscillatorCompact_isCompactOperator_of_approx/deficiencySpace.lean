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

noncomputable def deficiencySpace (T : H →ₗ.[ℂ] H) (z : ℂ) :
    Submodule ℂ T.adjoint.domain :=
  LinearMap.ker (T.adjoint.toFun - z • T.adjoint.domain.subtype)

/-- **Deficiency-space membership = eigenvector of the adjoint.** -/
