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

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Frontier.Spectral

open RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Key intermediate lemma: for a unit vector `u`, the inner product `⟪u, P u⟫`
is bounded in absolute value by `‖P u‖` (Cauchy–Schwarz). -/

theorem gap_to_cancellation_hypotheses_satisfiable :
    ∃ (P : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
      (u : EuclideanSpace ℝ (Fin 2)) (S δ : ℝ),
      (∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫) ∧ (∀ x, P (P x) = P x) ∧ ‖u‖ = 1 ∧ 0 < δ ∧
      S = ⟪u, P u⟫ ∧ ‖P u‖ ≤ 1 - δ ∧ S ≠ 0 := by
  refine ⟨projFirst, witnessVec, 9 / 25, 2 / 5, projFirst_selfAdjoint, projFirst_idem,
    norm_witnessVec, by norm_num, inner_witnessVec_projFirst.symm, ?_, by norm_num⟩
  rw [norm_projFirst_witnessVec]
  norm_num

end Frontier.Spectral

#print axioms Frontier.Spectral.gap_to_cancellation_conditional
#print axioms Frontier.Spectral.gap_to_cancellation_hypotheses_satisfiable

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

