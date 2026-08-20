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
theorem gap_to_cancellation_conditional {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (P : V →L[ℝ] V) (u : V) (S delta : ℝ)
    (hPsa : ∀ x y : V, (inner ℝ (P x) y : ℝ) = (inner ℝ x (P y) : ℝ))
    (hPidem : ∀ x : V, P (P x) = P x) (hu : ‖u‖ = 1)
    (hdelta : 0 < delta) (hS : S = (inner ℝ u (P u) : ℝ))
    (hcontr : ‖P u‖ ≤ 1 - delta) :
    |S| ≤ 1 - delta := by
  have h1 : |S| ≤ ‖P u‖ := by
    rw [hS]
    exact abs_inner_unit_le_norm u (P u) hu
  exact h1.trans hcontr

/-- Non-vacuity check: the hypotheses of `gap_to_cancellation_conditional` are simultaneously
satisfiable (take `V = ℝ`, `P = 0`, `u = 1`, `S = 0`, `delta = 1/2`). -/
example : ∃ (P : ℝ →L[ℝ] ℝ) (u S delta : ℝ),
    (∀ x y : ℝ, (inner ℝ (P x) y : ℝ) = (inner ℝ x (P y) : ℝ)) ∧
    (∀ x : ℝ, P (P x) = P x) ∧ ‖u‖ = 1 ∧ 0 < delta ∧
    S = (inner ℝ u (P u) : ℝ) ∧ ‖P u‖ ≤ 1 - delta := by
  refine ⟨0, 1, 0, 1/2, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

end Frontier.Spectral

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

