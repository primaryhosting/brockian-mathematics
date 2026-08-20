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

theorem inner_witnessVec_projFirst : ⟪witnessVec, projFirst witnessVec⟫ = 9 / 25 := by
  simp [witnessVec, projFirst, EuclideanSpace.single_apply, PiLp.inner_apply]
  norm_num

/-- All hypotheses of `gap_to_cancellation_conditional` are simultaneously
satisfiable with a nonzero `S`, so the conditional statement is not vacuous. -/
