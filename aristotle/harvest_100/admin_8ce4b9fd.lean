import Mathlib

/-!
# Gap To Cancellation Conditional
Category: Frontier Spectral
Target: Frontier.Spectral.gap_to_cancellation_conditional
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier.Spectral

/--
**Conditional cancellation bridge.**

Setting: a real inner-product space `V`, a linear map `P : V →ₗ[ℝ] V` which is a
self-adjoint projection (the "gap projection"), a unit vector `u`, and a real number
`S` (the Liouville partial sum).

Hypotheses (both kept open, neither is discharged):

* `H1` : a spectral gap `0 < delta` together with the identity `S = ⟪u, P u⟫`;
* `H2` : the contraction bound `‖P u‖ ≤ 1 - delta`.

Conclusion: `|S| ≤ 1 - delta`.

The proof is Cauchy–Schwarz: `|⟪u, P u⟫| ≤ ‖u‖ * ‖P u‖ = ‖P u‖ ≤ 1 - delta`.

The structural hypotheses `_hP_idem` (idempotence) and `_hP_sa` (self-adjointness) are part of
the stated setting and are therefore retained, although the implication does not need them.
-/
theorem gap_to_cancellation_conditional
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : V →ₗ[ℝ] V) (u : V) (S delta : ℝ)
    (_hP_idem : ∀ x, P (P x) = P x)
    (_hP_sa : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y))
    (hu : ‖u‖ = 1)
    (H1 : 0 < delta ∧ S = inner ℝ u (P u))
    (H2 : ‖P u‖ ≤ 1 - delta) :
    |S| ≤ 1 - delta := by
  obtain ⟨-, hS⟩ := H1
  have hcs : |(inner ℝ u (P u) : ℝ)| ≤ ‖u‖ * ‖P u‖ := abs_real_inner_le_norm u (P u)
  rw [hS]
  calc |(inner ℝ u (P u) : ℝ)| ≤ ‖u‖ * ‖P u‖ := hcs
    _ = ‖P u‖ := by rw [hu, one_mul]
    _ ≤ 1 - delta := H2

/--
Non-vacuity check: the hypotheses of `gap_to_cancellation_conditional` are simultaneously
satisfiable (here with `V = ℝ`, `P = 0`, `u = 1`, `S = 0`, `delta = 1/2`), so the conditional
statement is not vacuous.
-/
example :
    (∀ x : ℝ, (0 : ℝ →ₗ[ℝ] ℝ) ((0 : ℝ →ₗ[ℝ] ℝ) x) = (0 : ℝ →ₗ[ℝ] ℝ) x) ∧
    (∀ x y : ℝ, inner ℝ ((0 : ℝ →ₗ[ℝ] ℝ) x) y = inner ℝ x ((0 : ℝ →ₗ[ℝ] ℝ) y)) ∧
    ‖(1 : ℝ)‖ = 1 ∧
    (0 < (1 / 2 : ℝ) ∧ (0 : ℝ) = inner ℝ (1 : ℝ) ((0 : ℝ →ₗ[ℝ] ℝ) 1)) ∧
    ‖(0 : ℝ →ₗ[ℝ] ℝ) 1‖ ≤ 1 - 1 / 2 := by
  norm_num

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

