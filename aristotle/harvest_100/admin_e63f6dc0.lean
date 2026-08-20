/-
# Gap To Cancellation Conditional
Category: Frontier Spectral
Target: Frontier.Spectral.gap_to_cancellation_conditional
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gap To Cancellation Conditional
Category: Frontier Spectral
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

Setting: a real inner product space `V`, a self-adjoint projection `P` (the gap
projection), a unit vector `u`, and a real number `S` (the Liouville partial sum).

Hypotheses kept open (not discharged):
* `hgap` : the spectral gap `δ > 0` together with the identity `S = ⟪u, P u⟫`;
* `hcontract` : the contraction bound `‖P u‖ ≤ 1 - δ`.

Conclusion: `|S| ≤ 1 - δ`, obtained from Cauchy–Schwarz.

The self-adjointness and idempotence hypotheses on `P` are part of the stated
setting; the argument itself uses only Cauchy–Schwarz, the unit-norm hypothesis
and the contraction bound. -/
theorem gap_to_cancellation_conditional
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : V →L[ℝ] V) (u : V) (S δ : ℝ)
    (hsa : ∀ x y : V, inner ℝ (P x) y = inner ℝ x (P y))
    (hproj : ∀ x : V, P (P x) = P x)
    (hu : ‖u‖ = 1)
    (hgap : 0 < δ ∧ S = inner ℝ u (P u))
    (hcontract : ‖P u‖ ≤ 1 - δ) :
    |S| ≤ 1 - δ := by
  obtain ⟨-, hS⟩ := hgap
  have hCS : |inner ℝ u (P u)| ≤ ‖u‖ * ‖P u‖ := abs_real_inner_le_norm u (P u)
  rw [hS]
  calc |inner ℝ u (P u)| ≤ ‖u‖ * ‖P u‖ := hCS
    _ = ‖P u‖ := by rw [hu, one_mul]
    _ ≤ 1 - δ := hcontract

end Frontier.Spectral

