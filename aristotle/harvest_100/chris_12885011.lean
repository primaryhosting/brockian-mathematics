import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian

/-! ## Setup: Euclidean norm, contractions and the trace norm by duality -/

/-- The Euclidean (ℓ²) norm of a real vector indexed by `Fin n`. -/
noncomputable def nrm {n : ℕ} (v : Fin n → ℝ) : ℝ := Real.sqrt (∑ i, (v i) ^ 2)

/-- A matrix is a contraction when it does not increase the Euclidean norm. -/
def IsContraction {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ v : Fin n → ℝ, nrm (B.mulVec v) ≤ nrm v

/-- The set of dual pairings `tr (B * A)` of `A` against contractions `B`. -/
def pairings {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Set ℝ :=
  {t : ℝ | ∃ B : Matrix (Fin n) (Fin n) ℝ, IsContraction B ∧ Matrix.trace (B * A) = t}

/-- The trace norm (nuclear norm, Schatten 1-norm) of a real square matrix, defined by
duality: the supremum of `tr (B * A)` over all contractions `B`. -/
noncomputable def traceNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup (pairings A)

/-- The matrix with entries `cos (x i - y j)`. -/
noncomputable def cosMatrix {n : ℕ} (x y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.cos (x i - y j)

/-- The matrix with entries `sin (x i - y j)`. -/
noncomputable def sinMatrix {n : ℕ} (x y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.sin (x i - y j)

/-- The matrix with entries `cos (x i + y j)`. -/
noncomputable def cosSumMatrix {n : ℕ} (x y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.cos (x i + y j)

/-! ## Basic facts about the Euclidean norm -/

lemma nrm_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ nrm v := Real.sqrt_nonneg _

lemma nrm_sq {n : ℕ} (v : Fin n → ℝ) : (nrm v) ^ 2 = ∑ i, (v i) ^ 2 := by
  apply Real.sq_sqrt; positivity

lemma nrm_neg {n : ℕ} (v : Fin n → ℝ) : (nrm fun i => -(v i)) = nrm v := by
  simp [nrm]

lemma abs_dot_le {n : ℕ} (v w : Fin n → ℝ) :
    |∑ i, v i * w i| ≤ nrm v * nrm w := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v w
  have h2 : (∑ i, v i * w i) ^ 2 ≤ (nrm v * nrm w) ^ 2 := by
    rw [mul_pow, nrm_sq, nrm_sq]; exact h
  calc |∑ i, v i * w i| = Real.sqrt ((∑ i, v i * w i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((nrm v * nrm w) ^ 2) := Real.sqrt_le_sqrt h2
    _ = nrm v * nrm w := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg (nrm_nonneg _) (nrm_nonneg _))]

lemma isContraction_zero {n : ℕ} : IsContraction (0 : Matrix (Fin n) (Fin n) ℝ) := by
  intro v
  rw [Matrix.zero_mulVec]
  simp [nrm]

lemma pairings_nonempty {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : (pairings A).Nonempty :=
  ⟨Matrix.trace ((0 : Matrix (Fin n) (Fin n) ℝ) * A), 0, isContraction_zero, rfl⟩

/-! ## The dual pairing against a matrix of rank at most two -/

/-- The pairing of a contraction with a rank-≤2 matrix is bounded by the sum of the
products of the norms of the factors. -/
lemma abs_trace_le_of_decomp {n : ℕ} (a b c d : Fin n → ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : IsContraction B) :
    |Matrix.trace (B * Matrix.of fun i j => a i * b j + c i * d j)| ≤
      nrm a * nrm b + nrm c * nrm d := by
  have hkey : Matrix.trace (B * Matrix.of fun i j => a i * b j + c i * d j)
      = (∑ i, b i * (B.mulVec a) i) + (∑ i, d i * (B.mulVec c) i) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply,
      Matrix.mulVec, dotProduct, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [hkey]
  refine (abs_add_le _ _).trans ?_
  gcongr ?_ + ?_
  · exact (abs_dot_le b (B.mulVec a)).trans (by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hB a) (nrm_nonneg b))
  · exact (abs_dot_le d (B.mulVec c)).trans (by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hB c) (nrm_nonneg d))

lemma bddAbove_pairings_of_decomp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (a b c d : Fin n → ℝ)
    (hA : A = Matrix.of fun i j => a i * b j + c i * d j) : BddAbove (pairings A) := by
  refine ⟨nrm a * nrm b + nrm c * nrm d, ?_⟩
  rintro t ⟨B, hB, rfl⟩
  subst hA
  exact (le_abs_self _).trans (abs_trace_le_of_decomp a b c d B hB)

/-- Trace-norm bound for a matrix presented as a sum of two rank-one matrices. -/
lemma traceNorm_le_of_decomp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (a b c d : Fin n → ℝ)
    (hA : A = Matrix.of fun i j => a i * b j + c i * d j) :
    traceNorm A ≤ nrm a * nrm b + nrm c * nrm d := by
  refine csSup_le (pairings_nonempty A) ?_
  rintro t ⟨B, hB, rfl⟩
  subst hA
  exact (le_abs_self _).trans (abs_trace_le_of_decomp a b c d B hB)

/-! ## Norm bookkeeping for phase vectors -/

lemma nrm_cos_sq_add_nrm_sin_sq {n : ℕ} (x : Fin n → ℝ) :
    (nrm fun i => Real.cos (x i)) ^ 2 + (nrm fun i => Real.sin (x i)) ^ 2 = n := by
  rw [nrm_sq, nrm_sq, ← Finset.sum_add_distrib]
  simp [Real.cos_sq_add_sin_sq]

lemma four_norm_bound {n : ℕ} (p q r s : ℝ)
    (h1 : p ^ 2 + q ^ 2 = n) (h2 : r ^ 2 + s ^ 2 = n) : p * r + q * s ≤ n := by
  nlinarith [sq_nonneg (p * s - q * r), sq_nonneg (p * r + q * s),
    Nat.cast_nonneg (α := ℝ) n]

/-! ## The trace-norm bounds -/

/-- **Trace-norm bound for the cosine matrix.**  For any phases `x, y : Fin n → ℝ`, the
matrix with entries `cos (x i - y j)` has trace norm at most `n`. -/
theorem CosTraceNorm1279 {n : ℕ} (x y : Fin n → ℝ) :
    traceNorm (cosMatrix x y) ≤ n := by
  refine le_trans (traceNorm_le_of_decomp _ (fun i => Real.cos (x i)) (fun j => Real.cos (y j))
    (fun i => Real.sin (x i)) (fun j => Real.sin (y j)) ?_) ?_
  · ext i j
    simp [cosMatrix, Real.cos_sub]
  · exact four_norm_bound _ _ _ _ (nrm_cos_sq_add_nrm_sin_sq x) (nrm_cos_sq_add_nrm_sin_sq y)

/-- The analogous bound for the sine matrix `sin (x i - y j)`. -/
theorem SinTraceNorm1279 {n : ℕ} (x y : Fin n → ℝ) :
    traceNorm (sinMatrix x y) ≤ n := by
  refine le_trans (traceNorm_le_of_decomp _ (fun i => Real.sin (x i)) (fun j => Real.cos (y j))
    (fun i => Real.cos (x i)) (fun j => -Real.sin (y j)) ?_) ?_
  · ext i j
    simp [sinMatrix, Real.sin_sub]
    ring
  · rw [show (fun j => -Real.sin (y j)) = (fun j => -((fun j => Real.sin (y j)) j)) from rfl,
      nrm_neg]
    exact four_norm_bound _ _ _ _
      (by rw [add_comm]; exact nrm_cos_sq_add_nrm_sin_sq x) (nrm_cos_sq_add_nrm_sin_sq y)

/-- The analogous bound for the matrix `cos (x i + y j)`. -/
theorem CosSumTraceNorm1279 {n : ℕ} (x y : Fin n → ℝ) :
    traceNorm (cosSumMatrix x y) ≤ n := by
  refine le_trans (traceNorm_le_of_decomp _ (fun i => Real.cos (x i)) (fun j => Real.cos (y j))
    (fun i => Real.sin (x i)) (fun j => -Real.sin (y j)) ?_) ?_
  · ext i j
    simp [cosSumMatrix, Real.cos_add]
    ring
  · rw [show (fun j => -Real.sin (y j)) = (fun j => -((fun j => Real.sin (y j)) j)) from rfl,
      nrm_neg]
    exact four_norm_bound _ _ _ _ (nrm_cos_sq_add_nrm_sin_sq x) (nrm_cos_sq_add_nrm_sin_sq y)

/-! ## Sharpness -/

/-- The scaled all-ones matrix `(1/n) J` is a contraction. -/
lemma isContraction_allOnes {n : ℕ} :
    IsContraction (Matrix.of fun _ _ : Fin n => (1 / n : ℝ)) := by
  intro v
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [nrm]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmv : ∀ i, (Matrix.of (fun _ _ : Fin n => (1 / n : ℝ))).mulVec v i
      = (∑ j, v j) / n := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, one_div]
    rw [← Finset.mul_sum]
    ring
  have hcs : (∑ j, v j) ^ 2 ≤ n * ∑ j, (v j) ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin n => (1 : ℝ)) v
    simpa using this
  have hle : ∑ _i : Fin n, ((∑ j, v j) / n) ^ 2 ≤ ∑ i, (v i) ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_pow]
    have hEq : (n : ℝ) * ((∑ j, v j) ^ 2 / (n : ℝ) ^ 2) = (∑ j, v j) ^ 2 / n := by field_simp
    rw [hEq, div_le_iff₀ hn']
    nlinarith [hcs]
  simp only [nrm]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ((Matrix.of (fun _ _ : Fin n => (1 / n : ℝ))).mulVec v i) ^ 2
      = ∑ _i : Fin n, ((∑ j, v j) / n) ^ 2 := by
        exact Finset.sum_congr rfl (fun i _ => by rw [hmv i])
    _ ≤ ∑ i, (v i) ^ 2 := hle

/-- The bound `n` is attained: for zero phases the cosine matrix is the all-ones
matrix, whose trace norm is exactly `n`. -/
theorem CosTraceNorm1279_sharp {n : ℕ} :
    traceNorm (cosMatrix (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (0 : ℝ))) = n := by
  refine le_antisymm (CosTraceNorm1279 _ _) ?_
  have hbdd : BddAbove (pairings (cosMatrix (fun _ : Fin n => (0 : ℝ))
      (fun _ : Fin n => (0 : ℝ)))) := by
    refine bddAbove_pairings_of_decomp _ (fun i => Real.cos 0) (fun j => Real.cos 0)
      (fun i => Real.sin 0) (fun j => Real.sin 0) ?_
    ext i j
    simp [cosMatrix]
  have hmem : (n : ℝ) ∈ pairings (cosMatrix (fun _ : Fin n => (0 : ℝ))
      (fun _ : Fin n => (0 : ℝ))) := by
    refine ⟨Matrix.of fun _ _ : Fin n => (1 / n : ℝ), isContraction_allOnes, ?_⟩
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    have hn' : (n : ℝ) ≠ 0 := by positivity
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply, cosMatrix,
      sub_zero, Real.cos_zero, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  exact le_csSup hbdd hmem

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

