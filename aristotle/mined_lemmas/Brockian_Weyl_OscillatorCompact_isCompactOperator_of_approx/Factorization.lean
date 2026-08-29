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

noncomputable def Factorization.ofCompact (R : H →L[ℂ] H)
    (hR : IsCompactOperator R) : Factorization R H where
  embedding := R
  lift := ContinuousLinearMap.id ℂ H
  compact_embedding := hR
  factorization := by ext x; rfl

omit [CompleteSpace H] in
/-- Both unit-shift resolvents are compact once each has a weighted-Rellich
factorization. -/
