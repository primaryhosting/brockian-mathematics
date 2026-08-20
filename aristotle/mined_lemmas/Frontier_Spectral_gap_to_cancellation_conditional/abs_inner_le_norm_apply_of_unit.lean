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

theorem abs_inner_le_norm_apply_of_unit (P : V →ₗ[ℝ] V) (u : V) (hu : ‖u‖ = 1) :
    |⟪u, P u⟫| ≤ ‖P u‖ := by
  have h := abs_real_inner_le_norm u (P u)
  rwa [hu, one_mul] at h

/-- **Gap to cancellation (conditional).**

Setting: a real inner-product space `V`, a self-adjoint projection `P` (the gap
projection), a unit vector `u`, and a real number `S` (the Liouville partial sum).

Hypotheses:
* `hδ : 0 < δ` — a spectral gap;
* `hS : S = ⟪u, P u⟫` — the partial sum is realized as a diagonal matrix element;
* `hPu : ‖P u‖ ≤ 1 - δ` — the contraction bound.

Conclusion: `|S| ≤ 1 - δ`.

Both hypotheses `hS` and `hPu` are kept open (nothing is discharged here); the
statement is the implication only.  The structural hypotheses on `P`
(self-adjointness `hPsa` and idempotence `hPidem`) and the positivity of the gap
`hδ` are part of the requested setting; they are not needed for this particular
implication, whose proof is Cauchy–Schwarz. -/
