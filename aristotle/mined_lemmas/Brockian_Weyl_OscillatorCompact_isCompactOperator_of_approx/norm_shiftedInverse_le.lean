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

theorem norm_shiftedInverse_le (S : H →ₗ.[ℂ] H) (z : ℂ) (hS : IsSymmetric S)
    (hz : |z.im| = 1) (hsurj : ∀ y : H, ∃ v : S.domain, S v - z • (v : H) = y) :
    ‖shiftedInverse S z hS hz hsurj‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- **The canonical unit-shift resolvents of the closure of an essentially
self-adjoint symmetric operator.** -/
