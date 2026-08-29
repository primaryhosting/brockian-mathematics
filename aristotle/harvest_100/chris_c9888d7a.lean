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

Setting: a real inner-product space `V`, a linear operator `P : V →ₗ[ℝ] V` which is a
self-adjoint projection (`hsa`, `hproj`), a unit vector `u`, and a real number `S`
(the "Liouville partial sum").

Hypotheses (both left open, neither discharged):
* `H1` : there is a spectral gap `δ > 0` and `S = ⟪u, P u⟫`;
* `H2` : the contraction bound `‖P u‖ ≤ 1 - δ`.

Conclusion: `|S| ≤ 1 - δ`.

The proof is Cauchy–Schwarz: `|⟪u, P u⟫| ≤ ‖u‖ * ‖P u‖ = ‖P u‖ ≤ 1 - δ`.

The self-adjointness and idempotence hypotheses `hsa`, `hproj` are part of the stated
setting but are not needed for this implication; they are kept for faithfulness to the
statement. -/
theorem gap_to_cancellation_conditional
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : V →ₗ[ℝ] V)
    (hsa : ∀ x y : V, (inner ℝ (P x) y : ℝ) = (inner ℝ x (P y) : ℝ))
    (hproj : ∀ x : V, P (P x) = P x)
    (u : V) (hu : ‖u‖ = 1)
    (S δ : ℝ)
    (H1 : 0 < δ ∧ S = (inner ℝ u (P u) : ℝ))
    (H2 : ‖P u‖ ≤ 1 - δ) :
    |S| ≤ 1 - δ := by
  obtain ⟨hδ, hS⟩ := H1
  have hCS : |(inner ℝ u (P u) : ℝ)| ≤ ‖u‖ * ‖P u‖ := abs_real_inner_le_norm u (P u)
  rw [hS]
  calc |(inner ℝ u (P u) : ℝ)| ≤ ‖u‖ * ‖P u‖ := hCS
    _ = ‖P u‖ := by rw [hu, one_mul]
    _ ≤ 1 - δ := H2

end Frontier.Spectral

