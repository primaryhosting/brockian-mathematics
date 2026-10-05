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

/-- **Conditional cancellation bridge.**
In a real inner-product space `V`, let `P` be a self-adjoint idempotent (the gap
projection), `u` a unit vector and `S : ℝ` the Liouville partial sum.
Assuming (H1) a spectral gap `delta > 0` together with the identity
`S = ⟪u, P u⟫`, and (H2) the contraction bound `‖P u‖ ≤ 1 - delta`,
we conclude `|S| ≤ 1 - delta`.  Both hypotheses are kept open.

The self-adjointness and idempotence assumptions on `P` are part of the stated
setting; they are retained here even though the Cauchy–Schwarz argument does not
need them. -/
theorem gap_to_cancellation_conditional
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : V →ₗ[ℝ] V) (u : V) (S delta : ℝ)
    (hP_selfadjoint : ∀ x y : V, inner ℝ (P x) y = inner ℝ x (P y))
    (hP_idem : ∀ x : V, P (P x) = P x)
    (hu : ‖u‖ = 1)
    (H1 : 0 < delta ∧ S = inner ℝ u (P u))
    (H2 : ‖P u‖ ≤ 1 - delta) :
    |S| ≤ 1 - delta := by
  obtain ⟨-, hS⟩ := H1
  subst hS
  calc |inner ℝ u (P u)| ≤ ‖u‖ * ‖P u‖ := abs_real_inner_le_norm u (P u)
    _ = ‖P u‖ := by rw [hu, one_mul]
    _ ≤ 1 - delta := H2

/-- Non-vacuity witness: the hypotheses of `gap_to_cancellation_conditional`
are simultaneously satisfiable (take `V = ℝ`, `P = 0`, `u = 1`, `S = 0`,
`delta = 1/2`). -/
theorem gap_to_cancellation_hypotheses_satisfiable :
    ∃ (P : ℝ →ₗ[ℝ] ℝ) (u : ℝ) (S delta : ℝ),
      (∀ x y : ℝ, inner ℝ (P x) y = inner ℝ x (P y)) ∧
      (∀ x : ℝ, P (P x) = P x) ∧ ‖u‖ = 1 ∧
      (0 < delta ∧ S = inner ℝ u (P u)) ∧ ‖P u‖ ≤ 1 - delta := by
  exact ⟨0, 1, 0, 1/2, fun x y => by simp, fun x => by simp, by norm_num,
    ⟨by norm_num, by simp⟩, by norm_num⟩

end Frontier.Spectral

#print axioms Frontier.Spectral.gap_to_cancellation_conditional
#print axioms Frontier.Spectral.gap_to_cancellation_hypotheses_satisfiable

