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

theorem norm_le_norm_shifted {S : H →ₗ.[ℂ] H} (hS : IsSymmetric S) {z : ℂ}
    (hz : |z.im| = 1) (v : S.domain) : ‖(v : H)‖ ≤ ‖S v - z • (v : H)‖ := by
  have h := hS.norm_sub_smul_ge v z
  rwa [hz, one_mul] at h

omit [CompleteSpace H] in
/-- The shifted operator is injective. -/
