/-
# Gap To Cancellation Conditional
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.gap_to_cancellation_conditional
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gap To Cancellation Conditional
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.gap_to_cancellation_conditional
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Frontier.Spectral

open RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Key intermediate lemma: for a unit vector `u`, the inner product `⟪u, P u⟫`
is bounded in absolute value by `‖P u‖` (Cauchy–Schwarz). -/

theorem gap_to_cancellation_conditional
    (P : V →ₗ[ℝ] V) (u : V) (S δ : ℝ)
    (hPsa : ∀ x y : V, ⟪P x, y⟫ = ⟪x, P y⟫)
    (hPidem : ∀ x : V, P (P x) = P x)
    (hu : ‖u‖ = 1)
    (hδ : 0 < δ)
    (hS : S = ⟪u, P u⟫)
    (hPu : ‖P u‖ ≤ 1 - δ) :
    |S| ≤ 1 - δ := by
  have h : |⟪u, P u⟫| ≤ ‖P u‖ := abs_inner_le_norm_apply_of_unit P u hu
  rw [hS]
  exact h.trans hPu

/-! ### Non-vacuity: the hypotheses are simultaneously satisfiable

We exhibit a concrete instance in which all hypotheses of
`gap_to_cancellation_conditional` hold with `S ≠ 0`, so the implication is not
vacuous: `V = EuclideanSpace ℝ (Fin 2)`, `P` the orthogonal projection onto the
first coordinate axis, `u = (3/5, 4/5)`, `S = 9/25`, `δ = 2/5`. -/

/-- The orthogonal projection of `EuclideanSpace ℝ (Fin 2)` onto the first axis. -/
