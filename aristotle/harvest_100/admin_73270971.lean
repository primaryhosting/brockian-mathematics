import Mathlib

/-!
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
namespace Brockian

open Matrix

/-- The planar rotation matrix by angle `θ`. -/
noncomputable def rot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/-- Each diagonal entry of a real orthogonal matrix has absolute value at most `1`
(its columns are unit vectors). -/
lemma abs_diag_le_one_of_orthogonal {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (h : Aᵀ * A = 1) (i : n) : |A i i| ≤ 1 := by
  have hcol : ∑ j, A j i * A j i = 1 := by
    have := congrArg (fun M => M i i) h
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have hle : A i i * A i i ≤ ∑ j, A j i * A j i :=
    Finset.single_le_sum (f := fun j => A j i * A j i)
      (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
  rw [hcol] at hle
  exact abs_le_one_iff_mul_self_le_one.mpr hle

/-- Trace-norm bound: for a real orthogonal matrix all singular values are `1`, so the
trace norm equals the dimension and `|tr A| ≤ card n`. -/
lemma abs_trace_le_card_of_orthogonal {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (h : Aᵀ * A = 1) : |A.trace| ≤ (Fintype.card n : ℝ) := by
  calc |A.trace| = |∑ i, A i i| := rfl
    _ ≤ ∑ i, |A i i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => abs_diag_le_one_of_orthogonal A h i
    _ = (Fintype.card n : ℝ) := by simp [Finset.card_univ]

/-- The rotation matrix is orthogonal. -/
lemma rot_orthogonal (θ : ℝ) : (rot θ)ᵀ * rot θ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The trace of the rotation matrix is `2 cos θ`. -/
lemma trace_rot (θ : ℝ) : (rot θ).trace = 2 * Real.cos θ := by
  simp [rot, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]
  ring

/--
**Cos Trace Norm 1597.**

For every angle `θ`, the planar rotation matrix `rot θ` is orthogonal, its trace equals
`2 cos θ`, and this trace is bounded in absolute value by its trace norm, namely the
dimension `2`; equality holds exactly when `cos θ = ±1`.
-/
theorem CosTraceNorm1597 (θ : ℝ) :
    (rot θ)ᵀ * rot θ = 1 ∧ (rot θ).trace = 2 * Real.cos θ ∧
      |(rot θ).trace| ≤ 2 ∧ (|(rot θ).trace| = 2 ↔ Real.cos θ = 1 ∨ Real.cos θ = -1) := by
  refine ⟨rot_orthogonal θ, trace_rot θ, ?_, ?_⟩
  · have := abs_trace_le_card_of_orthogonal (rot θ) (rot_orthogonal θ)
    simpa using this
  · rw [trace_rot, abs_mul]
    constructor
    · intro h
      have : |Real.cos θ| = 1 := by
        rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at h
        linarith
      rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp this with h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
    · rintro (h | h) <;> simp [h]

end Brockian

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

