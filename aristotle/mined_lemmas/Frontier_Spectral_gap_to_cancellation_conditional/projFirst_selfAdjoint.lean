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

theorem projFirst_selfAdjoint (x y : EuclideanSpace ℝ (Fin 2)) :
    ⟪projFirst x, y⟫ = ⟪x, projFirst y⟫ := by
  simp [projFirst, PiLp.inner_apply, EuclideanSpace.single_apply]

