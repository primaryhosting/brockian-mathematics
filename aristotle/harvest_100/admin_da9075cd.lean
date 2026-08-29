/-
# Gap To Cancellation Conditional
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.gap_to_cancellation_conditional
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

namespace Frontier.Spectral

/--
**Conditional bridge: spectral gap ⟹ cancellation.**

Setting: a real inner-product space `V`, a self-adjoint projection `P` (the gap
projection), a unit vector `u`, and a real number `S` (the Liouville partial sum).

Hypotheses kept open (neither is discharged here):
* `H1`: a gap `delta > 0` together with the identity `S = ⟪u, P u⟫_ℝ`;
* `H2`: the contraction bound `‖P u‖ ≤ 1 - delta`.

Conclusion: `|S| ≤ 1 - delta`.

The proof is Cauchy–Schwarz: `|⟪u, P u⟫| ≤ ‖u‖ * ‖P u‖ = ‖P u‖ ≤ 1 - delta`.

The structural assumptions on `P` (self-adjointness and idempotence) are part of
the setting described in the statement; they are not needed for this implication,
which only uses `‖u‖ = 1` and the two hypotheses above.
-/
theorem gap_to_cancellation_conditional
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : V →L[ℝ] V) (hPsa : ∀ x y : V, inner ℝ (P x) y = inner ℝ x (P y))
    (hPidem : P.comp P = P)
    (u : V) (hu : ‖u‖ = 1) (S delta : ℝ)
    (H1 : 0 < delta ∧ S = inner ℝ u (P u))
    (H2 : ‖P u‖ ≤ 1 - delta) :
    |S| ≤ 1 - delta := by
  obtain ⟨-, hS⟩ := H1
  calc |S| = |(inner ℝ u (P u) : ℝ)| := by rw [hS]
    _ ≤ ‖u‖ * ‖P u‖ := abs_real_inner_le_norm u (P u)
    _ = ‖P u‖ := by rw [hu, one_mul]
    _ ≤ 1 - delta := H2

/-- Sanity check (non-vacuity): the hypotheses of
`gap_to_cancellation_conditional` are simultaneously satisfiable, so the
implication is not vacuously true. -/
example : ∃ (P : ℝ →L[ℝ] ℝ) (u : ℝ) (S delta : ℝ),
    (∀ x y : ℝ, inner ℝ (P x) y = inner ℝ x (P y)) ∧ P.comp P = P ∧
      ‖u‖ = 1 ∧ (0 < delta ∧ S = inner ℝ u (P u)) ∧ ‖P u‖ ≤ 1 - delta := by
  refine ⟨0, 1, 0, 1 / 2, fun x y => by simp, by ext; simp, by simp, ⟨by norm_num, by simp⟩,
    by norm_num⟩

end Frontier.Spectral

