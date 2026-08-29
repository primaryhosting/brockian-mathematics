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

theorem integrable_weight_sq (g : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => x ^ 2 * ‖g x‖ ^ 2) volume := by
  have h := schwartz_norm_mul_integrable (quadraticMulSchwartz g) g
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [quadraticMulSchwartz_apply]
  have hn : ‖((x : ℂ) ^ 2 : ℂ) * g x‖ = x ^ 2 * ‖g x‖ := by
    rw [norm_mul]
    congr 1
    rw [norm_pow]
    simp [sq_abs]
  rw [hn]; ring

/-! ### The main approximation estimate -/

/-- **The weighted-Rellich estimate for one Schwartz function.** -/
