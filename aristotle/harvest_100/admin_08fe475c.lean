import Mathlib

/-!
# Cos Trace Norm 4001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm4001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede any module doc comment, so the header
-- block above sits immediately after the single `import Mathlib` line.)

open scoped BigOperators
open scoped Real
open scoped Matrix

set_option maxRecDepth 10000

namespace Brockian

/-- The cosine kernel matrix `C i j = cos (x i - x j)` attached to a family of phases `x`. -/
noncomputable def cosKernel (n : ℕ) (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.cos (x i - x j)

@[simp] theorem cosKernel_apply (n : ℕ) (x : Fin n → ℝ) (i j : Fin n) :
    cosKernel n x i j = Real.cos (x i - x j) := rfl

/-- The quadratic form of the cosine kernel matrix is a sum of two squares: the kernel is the
Gram matrix of the unit vectors `(cos (x i), sin (x i))`. -/
theorem cos_kernel_quadratic_form (n : ℕ) (x v : Fin n → ℝ) :
    ∑ i, ∑ j, v i * v j * Real.cos (x i - x j)
      = (∑ i, v i * Real.cos (x i)) ^ 2 + (∑ i, v i * Real.sin (x i)) ^ 2 := by
  have hc : (∑ i, v i * Real.cos (x i)) ^ 2
      = ∑ i, ∑ j, (v i * Real.cos (x i)) * (v j * Real.cos (x j)) := by
    rw [sq, Finset.sum_mul_sum]
  have hs : (∑ i, v i * Real.sin (x i)) ^ 2
      = ∑ i, ∑ j, (v i * Real.sin (x i)) * (v j * Real.sin (x j)) := by
    rw [sq, Finset.sum_mul_sum]
  rw [hc, hs, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Real.cos_sub]
  ring

/-- The bilinear pairing `⟪v, C v⟫` written out as a double sum. -/
theorem cos_kernel_dotProduct (n : ℕ) (x v : Fin n → ℝ) :
    v ⬝ᵥ (cosKernel n x *ᵥ v) = ∑ i, ∑ j, v i * v j * Real.cos (x i - x j) := by
  simp only [dotProduct, cosKernel, Matrix.mulVec, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The cosine kernel matrix is positive semidefinite. -/
theorem cos_kernel_posSemidef (n : ℕ) (x : Fin n → ℝ) : (cosKernel n x).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v => ?_⟩
  · ext i j
    simp [cosKernel, Matrix.conjTranspose_apply, ← Real.cos_neg (x i - x j)]
  · rw [star_trivial, cos_kernel_dotProduct, cos_kernel_quadratic_form]
    positivity

/-- The trace of the cosine kernel matrix is `n`, since its diagonal entries are all `cos 0 = 1`. -/
theorem cos_kernel_trace (n : ℕ) (x : Fin n → ℝ) : (cosKernel n x).trace = n := by
  simp [Matrix.trace, Matrix.diag, cosKernel]

/-- Since the cosine kernel is positive semidefinite with trace `n`, its trace norm is `n`, and
hence its quadratic form is bounded by `n * ‖v‖²`. -/
theorem cos_kernel_quadratic_form_le (n : ℕ) (x v : Fin n → ℝ) :
    v ⬝ᵥ (cosKernel n x *ᵥ v) ≤ (n : ℝ) * ∑ i, (v i) ^ 2 := by
  rw [cos_kernel_dotProduct, cos_kernel_quadratic_form]
  have hc : (∑ i, v i * Real.cos (x i)) ^ 2
      ≤ (∑ i, (v i) ^ 2) * ∑ i, (Real.cos (x i)) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hs : (∑ i, v i * Real.sin (x i)) ^ 2
      ≤ (∑ i, (v i) ^ 2) * ∑ i, (Real.sin (x i)) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hsum : (∑ i, (Real.cos (x i)) ^ 2) + (∑ i, (Real.sin (x i)) ^ 2) = (n : ℝ) := by
    rw [← Finset.sum_add_distrib]
    simp [Real.cos_sq_add_sin_sq]
  have h := add_le_add hc hs
  rw [← mul_add, hsum, mul_comm] at h
  exact h

/-- **Cos Trace Norm 4001.**
For every family of phases `x : Fin 4001 → ℝ`, the cosine kernel matrix
`C i j = cos (x i - x j)` is positive semidefinite, its trace equals `4001` (so its trace norm,
the sum of its singular values, is `4001`), and its quadratic form obeys the corresponding
trace-norm bound `⟪v, C v⟫ ≤ 4001 * ‖v‖²`, with `0 ≤ ⟪v, C v⟫`, for every real vector `v`. -/
theorem CosTraceNorm4001 (x : Fin 4001 → ℝ) :
    (cosKernel 4001 x).PosSemidef ∧
    (cosKernel 4001 x).trace = 4001 ∧
    ∀ v : Fin 4001 → ℝ,
      0 ≤ v ⬝ᵥ (cosKernel 4001 x *ᵥ v) ∧
        v ⬝ᵥ (cosKernel 4001 x *ᵥ v) ≤ 4001 * ∑ i, (v i) ^ 2 := by
  refine ⟨cos_kernel_posSemidef 4001 x, ?_, fun v => ⟨?_, ?_⟩⟩
  · simpa using cos_kernel_trace 4001 x
  · simpa [star_trivial] using
      (Matrix.posSemidef_iff_dotProduct_mulVec.mp (cos_kernel_posSemidef 4001 x)).2 v
  · simpa using cos_kernel_quadratic_form_le 4001 x v

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

