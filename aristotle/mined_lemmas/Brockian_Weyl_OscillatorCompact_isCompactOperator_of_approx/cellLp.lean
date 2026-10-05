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

noncomputable def cellLp (Rr hh : ℝ) (j : ℕ) : L2R :=
  indicatorConstLp 2 (measurableSet_Ioc (a := -Rr + j * hh) (b := -Rr + (j + 1) * hh))
    measure_Ioc_lt_top.ne (1 : ℂ)

/-- The `L²` class of the step function with values `c j`. -/
