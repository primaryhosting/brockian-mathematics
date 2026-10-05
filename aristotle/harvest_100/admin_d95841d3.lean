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
open scoped InnerProductSpace

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

Setting: a real inner-product space `V`, a self-adjoint projection `P` (the gap
projection: `hPidem : P ∘ₗ P = P`, `hPsa : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫`), a unit
vector `u`, and a real number `S` (the Liouville partial sum).

Hypotheses (both left open, neither is discharged here):
* `H1`: a spectral gap `0 < δ` together with the identity `S = ⟪u, P u⟫`;
* `H2`: the contraction bound `‖P u‖ ≤ 1 - δ`.

Conclusion: `|S| ≤ 1 - δ`.

The proof is Cauchy–Schwarz: `|S| = |⟪u, P u⟫| ≤ ‖u‖ * ‖P u‖ = ‖P u‖ ≤ 1 - δ`.

Note: the structural hypotheses `hPidem`, `hPsa` and the strict positivity `0 < δ`
are part of the requested setting but turn out not to be needed for this
implication; they are kept in the statement as specified. -/
theorem gap_to_cancellation_conditional
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : V →ₗ[ℝ] V) (hPidem : P ∘ₗ P = P)
    (hPsa : ∀ x y : V, ⟪P x, y⟫_ℝ = ⟪x, P y⟫_ℝ)
    (u : V) (hu : ‖u‖ = 1) (S δ : ℝ)
    (hδ : 0 < δ) (hS : S = ⟪u, P u⟫_ℝ)
    (hcontr : ‖P u‖ ≤ 1 - δ) :
    |S| ≤ 1 - δ := by
  have hCS : |⟪u, P u⟫_ℝ| ≤ ‖u‖ * ‖P u‖ := abs_real_inner_le_norm u (P u)
  rw [hu, one_mul] at hCS
  rw [hS]
  exact hCS.trans hcontr

/-- The hypotheses of `gap_to_cancellation_conditional` are simultaneously satisfiable, so
the implication above is not vacuous: take `V = ℝ`, `P = 0`, `u = 1`, `S = 0`, `δ = 1/2`. -/
example : ∃ (P : ℝ →ₗ[ℝ] ℝ) (u : ℝ) (S δ : ℝ),
    P ∘ₗ P = P ∧ (∀ x y : ℝ, ⟪P x, y⟫_ℝ = ⟪x, P y⟫_ℝ) ∧ ‖u‖ = 1 ∧ 0 < δ ∧
      S = ⟪u, P u⟫_ℝ ∧ ‖P u‖ ≤ 1 - δ := by
  refine ⟨0, 1, 0, 1 / 2, by ext; simp, by simp, by simp, by norm_num, by simp, by norm_num⟩

end Frontier.Spectral

