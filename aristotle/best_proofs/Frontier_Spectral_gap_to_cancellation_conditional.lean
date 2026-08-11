/-
/-!
# Gap To Cancellation Conditional
Category: Frontier Spectral
Target: Frontier.Spectral.gap_to_cancellation_conditional
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

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

namespace Frontier
namespace Spectral

/-- **Conditional bridge: spectral gap ⟹ cancellation.**

Setting: a real inner-product space `V`, a self-adjoint projection `P` (the gap projection),
a unit vector `u`, and a real number `S` (the Liouville partial sum).

Hypotheses (both left open, neither is discharged here):
* `H1` : the gap `delta` is positive and `S = ⟪u, P u⟫`;
* `H2` : the contraction bound `‖P u‖ ≤ 1 - delta`.

Conclusion: `|S| ≤ 1 - delta`.

The proof is Cauchy–Schwarz: `|⟪u, P u⟫| ≤ ‖u‖ * ‖P u‖ = ‖P u‖ ≤ 1 - delta`.

The structural hypotheses `hP_idem` (idempotence) and `hP_sa` (self-adjointness) are part of the
stated setting; they turn out not to be needed for this implication and are kept only for
faithfulness to the statement. -/
theorem gap_to_cancellation_conditional
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : V →L[ℝ] V) (u : V) (S delta : ℝ)
    (hP_idem : ∀ x : V, P (P x) = P x)
    (hP_sa : ∀ x y : V, (inner ℝ (P x) y : ℝ) = (inner ℝ x (P y) : ℝ))
    (hu : ‖u‖ = 1)
    (H1 : 0 < delta ∧ S = (inner ℝ u (P u) : ℝ))
    (H2 : ‖P u‖ ≤ 1 - delta) :
    |S| ≤ 1 - delta := by
  obtain ⟨-, hS⟩ := H1
  have hcs : |(inner ℝ u (P u) : ℝ)| ≤ ‖u‖ * ‖P u‖ := abs_real_inner_le_norm u (P u)
  rw [hS]
  calc |(inner ℝ u (P u) : ℝ)| ≤ ‖u‖ * ‖P u‖ := hcs
    _ = ‖P u‖ := by rw [hu, one_mul]
    _ ≤ 1 - delta := H2

end Spectral
end Frontier

