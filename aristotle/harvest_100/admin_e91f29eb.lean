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

/-- **Gap ⟹ cancellation (conditional).**

Setting: a real inner product space `V`, a self-adjoint projection `P` (the gap projection),
a unit vector `u`, and a real number `S` (the Liouville partial sum).

Hypotheses kept open (they are *not* discharged here):
* `H1 : 0 < delta` together with `S = ⟪u, P u⟫_ℝ`;
* `H2 : ‖P u‖ ≤ 1 - delta` (the contraction bound supplied by the spectral gap).

Conclusion: `|S| ≤ 1 - delta`.

The proof is Cauchy–Schwarz (`abs_real_inner_le_norm` in Mathlib) combined with `‖u‖ = 1`.
The self-adjointness and idempotence hypotheses on `P` are part of the stated setting; they are
not needed for this particular implication, and are retained only for fidelity to the statement. -/
theorem gap_to_cancellation_conditional
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : V →L[ℝ] V) (hPsa : ∀ x y : V, inner ℝ (P x) y = inner ℝ x (P y))
    (hPidem : P ∘L P = P)
    (u : V) (hu : ‖u‖ = 1) (S delta : ℝ)
    (hdelta : 0 < delta)
    (H1 : S = inner ℝ u (P u))
    (H2 : ‖P u‖ ≤ 1 - delta) :
    |S| ≤ 1 - delta := by
  have hCS : |(inner ℝ u (P u) : ℝ)| ≤ ‖u‖ * ‖P u‖ := abs_real_inner_le_norm u (P u)
  rw [hu, one_mul] at hCS
  rw [H1]
  exact hCS.trans H2

/-- Sanity check: the hypotheses of `gap_to_cancellation_conditional` are simultaneously
satisfiable, so the implication above is not vacuous. Here `V = ℝ`, `P = 0`, `u = 1`, `S = 0`
and `delta = 1/2`. -/
example : ∃ (P : ℝ →L[ℝ] ℝ) (u : ℝ) (S delta : ℝ),
    (∀ x y : ℝ, inner ℝ (P x) y = inner ℝ x (P y)) ∧ P ∘L P = P ∧ ‖u‖ = 1 ∧ 0 < delta ∧
      S = inner ℝ u (P u) ∧ ‖P u‖ ≤ 1 - delta := by
  refine ⟨0, 1, 0, 1/2, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

end Frontier.Spectral

