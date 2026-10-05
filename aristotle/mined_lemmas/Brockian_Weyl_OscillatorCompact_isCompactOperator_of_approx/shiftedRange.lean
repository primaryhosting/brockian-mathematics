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

def shiftedRange (T : H →ₗ.[ℂ] H) (z : ℂ) : Submodule ℂ H :=
  LinearMap.range (T.toFun - z • T.domain.subtype)

omit [CompleteSpace H] in
