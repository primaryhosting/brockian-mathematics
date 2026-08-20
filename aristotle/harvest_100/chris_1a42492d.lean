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

namespace Frontier.Spectral

/-- **Gap to cancellation, conditional form.**

Setting: a real inner-product space `V`, a self-adjoint projection `P` (the gap projection),
a unit vector `u`, and a real number `S` (the Liouville partial sum).

Hypotheses (both kept open, neither is discharged):
* `hδ : 0 < delta` together with `hS : S = ⟪u, P u⟫_ℝ` (the gap identity, H1);
* `hcontr : ‖P u‖ ≤ 1 - delta` (the contraction bound, H2).

Conclusion: `|S| ≤ 1 - delta`.

The proof is Cauchy–Schwarz (`abs_real_inner_le_norm`) combined with `‖u‖ = 1`.
The structural hypotheses on `P` (`hPsa`: self-adjointness, `hPidem`: idempotence) are part of
the stated setting and are therefore kept, although the argument does not need them; likewise the
positivity `hδ` of the gap is not needed for the inequality itself. -/
theorem gap_to_cancellation_conditional
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : V →L[ℝ] V) (u : V) (S delta : ℝ)
    (hPsa : ∀ x y : V, (inner ℝ (P x) y : ℝ) = inner ℝ x (P y))
    (hPidem : ∀ x : V, P (P x) = P x)
    (hu : ‖u‖ = 1)
    (hδ : 0 < delta)
    (hS : S = (inner ℝ u (P u) : ℝ))
    (hcontr : ‖P u‖ ≤ 1 - delta) :
    |S| ≤ 1 - delta := by
  have hCS : |(inner ℝ u (P u) : ℝ)| ≤ ‖u‖ * ‖P u‖ := abs_real_inner_le_norm u (P u)
  rw [hS]
  calc |(inner ℝ u (P u) : ℝ)| ≤ ‖u‖ * ‖P u‖ := hCS
    _ = ‖P u‖ := by rw [hu, one_mul]
    _ ≤ 1 - delta := hcontr

/-- Non-vacuity check: the hypotheses of `gap_to_cancellation_conditional` are simultaneously
satisfiable (here with `V = ℝ`, `P` the zero projection, `u = 1`, `S = 0`, `delta = 1/2`). -/
example : ∃ (P : ℝ →L[ℝ] ℝ) (u S delta : ℝ),
    (∀ x y : ℝ, (inner ℝ (P x) y : ℝ) = inner ℝ x (P y)) ∧
    (∀ x : ℝ, P (P x) = P x) ∧ ‖u‖ = 1 ∧ 0 < delta ∧
    S = (inner ℝ u (P u) : ℝ) ∧ ‖P u‖ ≤ 1 - delta := by
  refine ⟨0, 1, 0, 1/2, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

end Frontier.Spectral

