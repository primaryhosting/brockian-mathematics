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
theorem abs_inner_le_norm_apply_of_unit (P : V →ₗ[ℝ] V) (u : V) (hu : ‖u‖ = 1) :
    |⟪u, P u⟫| ≤ ‖P u‖ := by
  have h := abs_real_inner_le_norm u (P u)
  rwa [hu, one_mul] at h

/-- **Gap to cancellation (conditional).**

Setting: a real inner-product space `V`, a self-adjoint projection `P` (the gap
projection), a unit vector `u`, and a real number `S` (the Liouville partial sum).

Hypotheses:
* `hδ : 0 < δ` — a spectral gap;
* `hS : S = ⟪u, P u⟫` — the partial sum is realized as a diagonal matrix element;
* `hPu : ‖P u‖ ≤ 1 - δ` — the contraction bound.

Conclusion: `|S| ≤ 1 - δ`.

Both hypotheses `hS` and `hPu` are kept open (nothing is discharged here); the
statement is the implication only.  The structural hypotheses on `P`
(self-adjointness `hPsa` and idempotence `hPidem`) and the positivity of the gap
`hδ` are part of the requested setting; they are not needed for this particular
implication, whose proof is Cauchy–Schwarz. -/
theorem gap_to_cancellation_conditional
    (P : V →ₗ[ℝ] V) (u : V) (S δ : ℝ)
    (hPsa : ∀ x y : V, ⟪P x, y⟫ = ⟪x, P y⟫)
    (hPidem : ∀ x : V, P (P x) = P x)
    (hu : ‖u‖ = 1)
    (hδ : 0 < δ)
    (hS : S = ⟪u, P u⟫)
    (hPu : ‖P u‖ ≤ 1 - δ) :
    |S| ≤ 1 - δ := by
  have h : |⟪u, P u⟫| ≤ ‖P u‖ := abs_inner_le_norm_apply_of_unit P u hu
  rw [hS]
  exact h.trans hPu

/-! ### Non-vacuity: the hypotheses are simultaneously satisfiable

We exhibit a concrete instance in which all hypotheses of
`gap_to_cancellation_conditional` hold with `S ≠ 0`, so the implication is not
vacuous: `V = EuclideanSpace ℝ (Fin 2)`, `P` the orthogonal projection onto the
first coordinate axis, `u = (3/5, 4/5)`, `S = 9/25`, `δ = 2/5`. -/

/-- The orthogonal projection of `EuclideanSpace ℝ (Fin 2)` onto the first axis. -/
noncomputable def projFirst :
    EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun x := EuclideanSpace.single (0 : Fin 2) (x 0)
  map_add' x y := by ext i; fin_cases i <;> simp [EuclideanSpace.single_apply]
  map_smul' c x := by ext i; fin_cases i <;> simp [EuclideanSpace.single_apply]

/-- The unit vector `(3/5, 4/5)`. -/
noncomputable def witnessVec : EuclideanSpace ℝ (Fin 2) := !₂[3 / 5, 4 / 5]

theorem projFirst_selfAdjoint (x y : EuclideanSpace ℝ (Fin 2)) :
    ⟪projFirst x, y⟫ = ⟪x, projFirst y⟫ := by
  simp [projFirst, PiLp.inner_apply, EuclideanSpace.single_apply]

theorem projFirst_idem (x : EuclideanSpace ℝ (Fin 2)) :
    projFirst (projFirst x) = projFirst x := by
  ext i; fin_cases i <;> simp [projFirst, EuclideanSpace.single_apply]

theorem norm_witnessVec : ‖witnessVec‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [witnessVec, Fin.sum_univ_two]
  norm_num

theorem norm_projFirst_witnessVec : ‖projFirst witnessVec‖ = 3 / 5 := by
  rw [EuclideanSpace.norm_eq]
  simp [witnessVec, projFirst, EuclideanSpace.single_apply]
  norm_num

theorem inner_witnessVec_projFirst : ⟪witnessVec, projFirst witnessVec⟫ = 9 / 25 := by
  simp [witnessVec, projFirst, EuclideanSpace.single_apply, PiLp.inner_apply]
  norm_num

/-- All hypotheses of `gap_to_cancellation_conditional` are simultaneously
satisfiable with a nonzero `S`, so the conditional statement is not vacuous. -/
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

