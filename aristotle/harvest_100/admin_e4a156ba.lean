import Mathlib

/-!
# Cos Trace Norm 4001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm4001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset

namespace Brockian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Unfolding of the unitary conjugation star-algebra automorphism used by the matrix
spectral theorem. -/
theorem conjStarAlgAut_apply (u : Matrix.unitaryGroup n ℂ) (x : Matrix n n ℂ) :
    (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ)) u x
      = (u : Matrix n n ℂ) * x * star (u : Matrix n n ℂ) := by
  simp [Unitary.conjStarAlgAut, Unitary.toUnits]
  rfl

/-- The cosine of a Hermitian matrix, defined by the (finite dimensional) continuous functional
calculus: conjugate the diagonal matrix of the cosines of the eigenvalues by the unitary of
eigenvectors. -/
noncomputable def hermCos {A : Matrix n n ℂ} (hA : A.IsHermitian) : Matrix n n ℂ :=
  (hA.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i => ((Real.cos (hA.eigenvalues i) : ℝ) : ℂ)) *
    star (hA.eigenvectorUnitary : Matrix n n ℂ)

/-- `hermCos hA` is again Hermitian. -/
theorem hermCos_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (hermCos hA).IsHermitian := by
  unfold Matrix.IsHermitian hermCos
  simp [conjTranspose_mul, Matrix.mul_assoc, diagonal_conjTranspose,
    Matrix.star_eq_conjTranspose, Pi.star_def, -Complex.ofReal_cos]

/-- Testing a diagonal matrix against a unitary one: the trace of `W * diagonal d` is a convex-type
combination of the entries of `d`, hence bounded by `∑ i, ‖d i‖`. -/
theorem norm_trace_mul_diagonal_le {W : Matrix n n ℂ} (hW : W ∈ Matrix.unitaryGroup n ℂ)
    (d : n → ℂ) : ‖(W * diagonal d).trace‖ ≤ ∑ i, ‖d i‖ := by
  rw [Matrix.trace]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
  rw [Matrix.diag_apply, Matrix.mul_diagonal, norm_mul]
  have h := entry_norm_bound_of_unitary hW i i
  nlinarith [norm_nonneg (d i), norm_nonneg (W i i)]

/-- Testing a unitarily-diagonalized matrix against an arbitrary unitary: conjugating moves the
test unitary onto the diagonal factor. -/
theorem norm_trace_mul_conj_diagonal_le {U V : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (hV : V ∈ Matrix.unitaryGroup n ℂ) (d : n → ℂ) :
    ‖(V * (U * diagonal d * star U)).trace‖ ≤ ∑ i, ‖d i‖ := by
  have hW : (star U * V * U) ∈ Matrix.unitaryGroup n ℂ :=
    mul_mem (mul_mem (Unitary.star_mem hU) hV) hU
  have h1 : (V * (U * diagonal d * star U)).trace = ((star U * V * U) * diagonal d).trace := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.trace_mul_cycle (V * U) (diagonal d) (star U)]
    simp [Matrix.mul_assoc]
  rw [h1]
  exact norm_trace_mul_diagonal_le hW d

/-- Key duality step: testing `hermCos hA` against an arbitrary unitary gives the sharp bound
by the sum of the absolute values of the cosines of the eigenvalues. -/
theorem norm_trace_mul_hermCos_le_sum {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {V : Matrix n n ℂ} (hV : V ∈ Matrix.unitaryGroup n ℂ) :
    ‖(V * hermCos hA).trace‖ ≤ ∑ i, |Real.cos (hA.eigenvalues i)| := by
  have h := norm_trace_mul_conj_diagonal_le (U := (hA.eigenvectorUnitary : Matrix n n ℂ))
    hA.eigenvectorUnitary.2 hV (fun i => ((Real.cos (hA.eigenvalues i) : ℝ) : ℂ))
  simpa [hermCos, Matrix.mul_assoc, -Complex.ofReal_cos, Complex.norm_real] using h

/-- **Cos Trace Norm 4001.**
For every Hermitian matrix `A` over `ℂ`, the trace norm of `cos A` is at most the dimension.
The statement is given in the dual (variational) form of the trace norm,
`‖M‖₁ = sup { ‖tr (V * M)‖ : V unitary }`: every unitary test `V` satisfies
`‖tr (V * cos A)‖ ≤ card n`. -/
theorem CosTraceNorm4001 {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {V : Matrix n n ℂ} (hV : V ∈ Matrix.unitaryGroup n ℂ) :
    ‖(V * hermCos hA).trace‖ ≤ (Fintype.card n : ℝ) := by
  refine le_trans (norm_trace_mul_hermCos_le_sum hA hV) ?_
  calc ∑ i, |Real.cos (hA.eigenvalues i)| ≤ ∑ _i : n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => Real.abs_cos_le_one _
    _ = (Fintype.card n : ℝ) := by simp [Finset.card_univ]

/-- The eigenvalues of the zero matrix all vanish. -/
theorem eigenvalues_zero_eq_zero (i : n) :
    (Matrix.isHermitian_zero (n := n) (α := ℂ)).eigenvalues i = 0 := by
  set hA := Matrix.isHermitian_zero (n := n) (α := ℂ) with hAdef
  have h := hA.spectral_theorem
  rw [conjStarAlgAut_apply] at h
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hU
  have h1 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hA.eigenvectorUnitary.2
  have hD : diagonal (Complex.ofReal ∘ hA.eigenvalues) = 0 := by
    have h3 := congrArg (fun M => star U * M * U) h
    simp only [Matrix.mul_assoc] at h3
    rw [← Matrix.mul_assoc (star U) U, h1, Matrix.one_mul] at h3
    simp at h3
    exact h3.symm
  simpa using congrFun (congrFun hD i) i

/-- The bound of `CosTraceNorm4001` is sharp: for `A = 0` we get `cos A = 1`, whose trace norm
is exactly `card n` (witnessed by the unitary `V = 1`). -/
theorem hermCos_zero : hermCos (A := (0 : Matrix n n ℂ)) Matrix.isHermitian_zero = 1 := by
  have h1 : (star (Matrix.isHermitian_zero (n := n) (α := ℂ)).eigenvectorUnitary.val) *
      ((Matrix.isHermitian_zero (n := n) (α := ℂ)).eigenvectorUnitary.val) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 (Matrix.isHermitian_zero (n := n) (α := ℂ)).eigenvectorUnitary.2
  have h2 : (Matrix.isHermitian_zero (n := n) (α := ℂ)).eigenvectorUnitary.val *
      star ((Matrix.isHermitian_zero (n := n) (α := ℂ)).eigenvectorUnitary.val) = 1 :=
    Matrix.mem_unitaryGroup_iff.1 (Matrix.isHermitian_zero (n := n) (α := ℂ)).eigenvectorUnitary.2
  simp only [hermCos, eigenvalues_zero_eq_zero, Real.cos_zero, Complex.ofReal_one,
    Matrix.diagonal_one, Matrix.mul_one, h2]

/-- Sharpness of `CosTraceNorm4001`: the trace-norm bound `card n` is attained at `A = 0`. -/
theorem CosTraceNorm4001_sharp :
    ‖((1 : Matrix n n ℂ) * hermCos (A := (0 : Matrix n n ℂ)) Matrix.isHermitian_zero).trace‖
      = (Fintype.card n : ℝ) := by
  rw [hermCos_zero, Matrix.one_mul, Matrix.trace_one]
  simp

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

