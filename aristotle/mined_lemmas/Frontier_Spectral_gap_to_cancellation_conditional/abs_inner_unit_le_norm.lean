import Mathlib
/-!
# Gap To Cancellation Conditional
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.gap_to_cancellation_conditional
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Frontier.Spectral

/-- Key intermediate lemma (Cauchy–Schwarz for a unit vector): for a unit vector `u`
and any vector `w` in a real inner product space, `|⟪u, w⟫| ≤ ‖w‖`. -/

theorem abs_inner_unit_le_norm {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u w : V) (hu : ‖u‖ = 1) : |(inner ℝ u w : ℝ)| ≤ ‖w‖ := by
  have h := abs_real_inner_le_norm u w
  simpa [hu] using h

/-- **Conditional cancellation bridge.**

Setting: a real inner product space `V`, a self-adjoint projection `P` (the gap projection),
a unit vector `u`, and a real number `S` (the Liouville partial sum).

Hypotheses (both kept open, neither is discharged):
* (H1) a spectral gap `0 < delta` together with the identity `S = ⟪u, P u⟫`;
* (H2) the contraction bound `‖P u‖ ≤ 1 - delta`.

Conclusion: `|S| ≤ 1 - delta`.

The hypotheses that `P` is a self-adjoint idempotent and that `0 < delta` are part of the
stated setting; they are recorded here even though the implication itself follows from
Cauchy–Schwarz applied to the unit vector `u` together with (H1) and (H2). -/
