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

theorem eq_of_shifted_eq {S : H →ₗ.[ℂ] H} (hS : IsSymmetric S) {z : ℂ}
    (hz : |z.im| = 1) {v w : S.domain}
    (h : S v - z • (v : H) = S w - z • (w : H)) : v = w := by
  have hvw : S (v - w) - z • ((v - w : S.domain) : H) = 0 := by
    have hmap : S (v - w) = S v - S w := LinearPMap.map_sub _ _ _
    have hcoe : ((v - w : S.domain) : H) = (v : H) - (w : H) := rfl
    rw [hmap, hcoe, smul_sub, sub_sub_sub_comm, h, sub_self]
  have hnorm := norm_le_norm_shifted hS hz (v - w)
  rw [hvw, norm_zero] at hnorm
  have h0 : ((v - w : S.domain) : H) = 0 := norm_le_zero_iff.mp hnorm
  exact sub_eq_zero.mp (Subtype.ext h0)

/-- The shifted range of the closure is closed. -/
