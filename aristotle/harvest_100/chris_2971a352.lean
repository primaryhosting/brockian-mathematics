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
open scoped Classical

namespace Frontier.Spectral

/-- **Conditional bridge: spectral gap ⟹ cancellation.**

Setting: a real inner-product space `V`, a continuous linear map `P : V →L[ℝ] V`
which is a self-adjoint projection (`⟪P x, y⟫ = ⟪x, P y⟫` and `P ∘ P = P`), a unit vector
`u`, and a real number `S` (the Liouville partial sum).

Hypotheses (both left open, neither is discharged):
* `H1` : there is a gap `delta > 0` together with the identity `S = ⟪u, P u⟫`;
* `H2` : the contraction bound `‖P u‖ ≤ 1 - delta`.

Conclusion: `|S| ≤ 1 - delta`.

The structural assumptions on `P` (self-adjointness and idempotence) are part of the
stated setting and are therefore kept, even though the implication holds without them.

The proof is Cauchy–Schwarz: `|⟪u, P u⟫| ≤ ‖u‖ * ‖P u‖ = ‖P u‖ ≤ 1 - delta`. -/
theorem gap_to_cancellation_conditional
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : V →L[ℝ] V)
    (hPsa : ∀ x y : V, (inner ℝ (P x) y : ℝ) = inner ℝ x (P y))
    (hPidem : ∀ v : V, P (P v) = P v)
    (u : V) (hu : ‖u‖ = 1) (S delta : ℝ)
    (H1 : 0 < delta ∧ S = inner ℝ u (P u))
    (H2 : ‖P u‖ ≤ 1 - delta) :
    |S| ≤ 1 - delta := by
  obtain ⟨_hdelta, hS⟩ := H1
  have hcs : |(inner ℝ u (P u) : ℝ)| ≤ ‖u‖ * ‖P u‖ := abs_real_inner_le_norm u (P u)
  rw [hS]
  calc |(inner ℝ u (P u) : ℝ)| ≤ ‖u‖ * ‖P u‖ := hcs
    _ = ‖P u‖ := by rw [hu, one_mul]
    _ ≤ 1 - delta := H2

end Frontier.Spectral

/-- The hypotheses of `gap_to_cancellation_conditional` are simultaneously satisfiable,
so the implication is not vacuous. -/
example : ∃ (P : ℝ →L[ℝ] ℝ) (u : ℝ) (S delta : ℝ),
    (∀ x y : ℝ, (inner ℝ (P x) y : ℝ) = inner ℝ x (P y)) ∧
    (∀ v : ℝ, P (P v) = P v) ∧ ‖u‖ = 1 ∧
    (0 < delta ∧ S = inner ℝ u (P u)) ∧ ‖P u‖ ≤ 1 - delta := by
  refine ⟨0, 1, 0, 1/2, ?_, ?_, ?_, ⟨by norm_num, ?_⟩, ?_⟩ <;>
    norm_num [RCLike.inner_apply]

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

