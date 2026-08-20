/-
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
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

namespace Brockian

/-- The squared Frobenius (Hilbert–Schmidt) norm of a square real matrix:
the sum of the squares of all its entries. -/
def frobSq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

/-- The plane rotation matrix by the angle `θ`. -/
noncomputable def rot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

/-- The diagonal of a matrix contributes at most the full Frobenius sum. -/
lemma sum_diag_sq_le_frobSq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∑ i, (A i i) ^ 2 ≤ frobSq A := by
  refine Finset.sum_le_sum ?_
  intro i _
  exact Finset.single_le_sum (f := fun j => (A i j) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)

/-- Cauchy–Schwarz trace bound: the absolute value of the trace of a real
`n × n` matrix is at most `√n` times its Frobenius norm. -/
lemma abs_trace_le_sqrt_mul_sqrt_frobSq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    |A.trace| ≤ Real.sqrt n * Real.sqrt (frobSq A) := by
  have hfrob : (0 : ℝ) ≤ frobSq A :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs : (A.trace) ^ 2 ≤ (n : ℝ) * frobSq A := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
      (fun _ => (1 : ℝ)) (fun i => A i i)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at h
    calc (A.trace) ^ 2 = (∑ i, A i i) ^ 2 := by rw [Matrix.trace]; simp [Matrix.diag]
      _ ≤ (n : ℝ) * ∑ i, (A i i) ^ 2 := h
      _ ≤ (n : ℝ) * frobSq A := by
          exact mul_le_mul_of_nonneg_left (sum_diag_sq_le_frobSq A) (Nat.cast_nonneg n)
  have h1 : |A.trace| = Real.sqrt ((A.trace) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
  rw [h1, ← Real.sqrt_mul (Nat.cast_nonneg n)]
  exact Real.sqrt_le_sqrt hcs

/-- The Frobenius norm of a rotation matrix is `√2`. -/
lemma frobSq_rot (θ : ℝ) : frobSq (rot θ) = 2 := by
  simp [frobSq, rot, Fin.sum_univ_two]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The trace of a rotation matrix is `2 cos θ`. -/
lemma trace_rot (θ : ℝ) : (rot θ).trace = 2 * Real.cos θ := by
  rw [rot, Matrix.trace_fin_two_of]; ring

/--
**Cos Trace Norm 2003.**

For every angle `θ`, the plane rotation `rot θ` has trace `2 cos θ`, and this trace
obeys the Cauchy–Schwarz trace-norm bound `|tr A| ≤ √n · ‖A‖_F` (here `n = 2`),
whose right-hand side equals `2`; consequently `|2 cos θ| ≤ 2`, with equality
exactly when `θ` is an integer multiple of `π`.
-/
theorem CosTraceNorm2003 (θ : ℝ) :
    (rot θ).trace = 2 * Real.cos θ ∧
    |(rot θ).trace| ≤ Real.sqrt 2 * Real.sqrt (frobSq (rot θ)) ∧
    Real.sqrt 2 * Real.sqrt (frobSq (rot θ)) = 2 ∧
    |2 * Real.cos θ| ≤ 2 ∧
    (|2 * Real.cos θ| = 2 ↔ ∃ k : ℤ, θ = k * Real.pi) := by
  have hn : Real.sqrt ((2 : ℕ) : ℝ) = Real.sqrt 2 := by norm_num
  have hb : |(rot θ).trace| ≤ Real.sqrt 2 * Real.sqrt (frobSq (rot θ)) := by
    have := abs_trace_le_sqrt_mul_sqrt_frobSq (rot θ)
    rwa [hn] at this
  have hrhs : Real.sqrt 2 * Real.sqrt (frobSq (rot θ)) = 2 := by
    rw [frobSq_rot]
    exact Real.mul_self_sqrt (by norm_num)
  refine ⟨trace_rot θ, hb, hrhs, ?_, ?_⟩
  · rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have := Real.abs_cos_le_one θ
    linarith
  · rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    constructor
    · intro h
      have hc : |Real.cos θ| = 1 := by linarith
      have hs : Real.sin θ = 0 := by
        nlinarith [Real.sin_sq_add_cos_sq θ, sq_abs (Real.cos θ), sq_nonneg (Real.sin θ)]
      obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 hs
      exact ⟨k, hk.symm⟩
    · rintro ⟨k, rfl⟩
      have : Real.sin (k * Real.pi) = 0 := by
        simp [Real.sin_int_mul_pi k]
      have hcos : Real.cos ((k : ℝ) * Real.pi) ^ 2 = 1 := by
        nlinarith [Real.sin_sq_add_cos_sq ((k : ℝ) * Real.pi)]
      have : |Real.cos ((k : ℝ) * Real.pi)| = 1 := by
        have := sq_abs (Real.cos ((k : ℝ) * Real.pi))
        nlinarith [abs_nonneg (Real.cos ((k : ℝ) * Real.pi))]
      rw [this]; ring

/-! ### Extension of the family: trace bounds for orthogonal matrices -/

/-- An orthogonal matrix has squared Frobenius norm equal to its size. -/
lemma frobSq_of_orthogonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : A * A.transpose = 1) : frobSq A = n := by
  have h1 : (A * A.transpose).trace = ((1 : Matrix (Fin n) (Fin n) ℝ)).trace := by rw [h]
  rw [Matrix.trace_one, Fintype.card_fin] at h1
  calc frobSq A = ∑ i, ∑ j, A i j * (A.transpose) j i := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.transpose_apply]; ring
    _ = (A * A.transpose).trace := by
        rw [Matrix.trace]
        exact (Finset.sum_congr rfl fun i _ => by
          simp [Matrix.diag, Matrix.mul_apply]).symm
    _ = (n : ℝ) := h1

/-- **New trace-norm bound.** The trace of a real orthogonal `n × n` matrix is
bounded in absolute value by `n`. -/
theorem abs_trace_le_card_of_orthogonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : A * A.transpose = 1) : |A.trace| ≤ n := by
  have hb := abs_trace_le_sqrt_mul_sqrt_frobSq A
  rw [frobSq_of_orthogonal A h] at hb
  rwa [Real.mul_self_sqrt (Nat.cast_nonneg n)] at hb

/-- The plane rotation is orthogonal. -/
lemma rot_mul_transpose (θ : ℝ) : rot θ * (rot θ).transpose = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The rotation instance of the orthogonal trace bound: `|2 cos θ| ≤ 2`. -/
theorem abs_trace_rot_le_two (θ : ℝ) : |(rot θ).trace| ≤ 2 := by
  have := abs_trace_le_card_of_orthogonal (rot θ) (rot_mul_transpose θ)
  norm_num at this
  exact this

end Brockian

