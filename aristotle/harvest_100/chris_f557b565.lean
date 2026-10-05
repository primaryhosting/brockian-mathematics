/- (Lean requires `import` to precede any module docstring `/-! ... -/`, so this header
is given as a plain block comment.)
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Complex Real

/-- The adjacency matrix of the cycle graph `C₇`, with vertices indexed by `Fin 7`
(where addition is modulo `7`): vertices `i` and `j` are adjacent iff they differ by one
step around the cycle. -/
def C7 : Matrix (Fin 7) (Fin 7) ℝ := fun i j => if i + 1 = j ∨ j + 1 = i then 1 else 0

/-- `C7` is symmetric. -/
lemma C7_transpose : C7ᵀ = C7 := by
  ext i j
  simp only [Matrix.transpose_apply, C7]
  exact if_congr or_comm rfl rfl

/-- Every vertex of `C₇` has degree `2`. -/
lemma C7_row_sum (i : Fin 7) : ∑ j, C7 i j = 2 := by
  simp only [C7, Fin.sum_univ_seven]
  fin_cases i <;> simp +decide <;> norm_num

/-- The adjacency matrix of `C₇`, viewed over `ℂ`. -/
def C7C : Matrix (Fin 7) (Fin 7) ℂ := fun i j => if i + 1 = j ∨ j + 1 = i then 1 else 0

/-- A primitive 7th root of unity. -/
noncomputable def w : ℂ := Complex.exp (2 * π * I / 7)

lemma w_primitive : IsPrimitiveRoot w 7 := by
  simpa [w] using Complex.isPrimitiveRoot_exp 7 (by norm_num)

lemma w_pow_seven : w ^ 7 = 1 := w_primitive.pow_eq_one

/-- The Fourier / Vandermonde matrix built from the powers of `w`. -/
noncomputable def Fm : Matrix (Fin 7) (Fin 7) ℂ :=
  Matrix.vandermonde (fun i : Fin 7 => w ^ (i : ℕ))

/-- The `k`-th Hückel eigenvalue of `C₇`, namely `2 cos (2πk/7)`. -/
noncomputable def ev (k : Fin 7) : ℝ := 2 * Real.cos (2 * π * k / 7)

/-- Euler's formula: `2 cos (2πk/7) = wᵏ + w⁻ᵏ`. -/
lemma ev_eq (k : Fin 7) : ((ev k : ℝ) : ℂ) = w ^ (k : ℕ) + (w ^ (k : ℕ))⁻¹ := by
  have h : w ^ (k : ℕ) = Complex.exp (((2 * π * (k : ℕ) / 7 : ℝ) : ℂ) * I) := by
    rw [w, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h, ← Complex.exp_neg, ev]
  push_cast
  rw [Complex.two_cos]
  ring_nf

lemma Fm_det_ne_zero : Fm.det ≠ 0 := by
  rw [Fm, Matrix.det_vandermonde_ne_zero_iff]
  intro i j hij
  exact Fin.ext (w_primitive.pow_inj i.isLt j.isLt hij)

/-- The Fourier matrix diagonalizes the circulant adjacency matrix of `C₇`. -/
lemma C7C_mul_Fm : C7C * Fm = Fm * Matrix.diagonal (fun k : Fin 7 => ((ev k : ℝ) : ℂ)) := by
  ext i k
  rw [Matrix.mul_diagonal, ev_eq]
  have hF : ∀ j : Fin 7, Fm j k = (w ^ (k : ℕ)) ^ (j : ℕ) := by
    intro j; simp [Fm, Matrix.vandermonde_apply, ← pow_mul, Nat.mul_comm]
  have h7 : (w ^ (k : ℕ)) ^ 7 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, w_pow_seven, one_pow]
  have hinv : (w ^ (k : ℕ))⁻¹ = (w ^ (k : ℕ)) ^ 6 :=
    inv_eq_of_mul_eq_one_right (by linear_combination h7)
  rw [Matrix.mul_apply, hinv]
  simp only [Fin.sum_univ_seven, hF, C7C]
  set x := w ^ (k : ℕ) with hxdef
  clear_value x
  fin_cases i <;> simp +decide
  · linear_combination -h7
  · linear_combination -x * h7
  · linear_combination -x ^ 2 * h7
  · linear_combination -x ^ 3 * h7
  · linear_combination -x ^ 4 * h7
  · linear_combination -(1 + x ^ 5) * h7

lemma diag_sub (μ : ℂ) :
    Matrix.diagonal (fun k : Fin 7 => ((ev k : ℝ) : ℂ)) - μ • (1 : Matrix (Fin 7) (Fin 7) ℂ)
      = Matrix.diagonal (fun k : Fin 7 => ((ev k : ℝ) : ℂ) - μ) := by
  ext i j
  by_cases h : i = j <;> simp [h]

/-- The characteristic determinant of the adjacency matrix of `C₇` factors completely. -/
lemma det_charpoly (μ : ℂ) :
    (C7C - μ • (1 : Matrix (Fin 7) (Fin 7) ℂ)).det = ∏ k : Fin 7, (((ev k : ℝ) : ℂ) - μ) := by
  have key : (C7C - μ • (1 : Matrix (Fin 7) (Fin 7) ℂ)) * Fm
      = Fm * (Matrix.diagonal (fun k : Fin 7 => ((ev k : ℝ) : ℂ))
          - μ • (1 : Matrix (Fin 7) (Fin 7) ℂ)) := by
    rw [sub_mul, mul_sub, C7C_mul_Fm, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
  have h := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, diag_sub, Matrix.det_diagonal] at h
  exact mul_right_cancel₀ Fm_det_ne_zero (h.trans (mul_comm _ _))

lemma map_C7 : (Complex.ofRealHom).mapMatrix C7 = C7C := by
  ext i j
  by_cases h : i + 1 = j ∨ j + 1 = i <;> simp [C7, C7C, h]

lemma map_C7_sub (μ : ℝ) :
    (Complex.ofRealHom).mapMatrix (C7 - μ • (1 : Matrix (Fin 7) (Fin 7) ℝ))
      = C7C - (μ : ℂ) • (1 : Matrix (Fin 7) (Fin 7) ℂ) := by
  rw [map_sub, map_C7]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h]

lemma real_det_eq (μ : ℝ) :
    ((C7 - μ • (1 : Matrix (Fin 7) (Fin 7) ℝ)).det : ℂ)
      = (C7C - (μ : ℂ) • (1 : Matrix (Fin 7) (Fin 7) ℂ)).det := by
  rw [show ((C7 - μ • (1 : Matrix (Fin 7) (Fin 7) ℝ)).det : ℂ)
      = Complex.ofRealHom ((C7 - μ • (1 : Matrix (Fin 7) (Fin 7) ℝ)).det) from rfl,
    RingHom.map_det, map_C7_sub]

/-- **Hückel theory for the cycle `C₇`.**  A real number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₇` if and only if `μ = 2 cos (2πk/7)` for some
`k ∈ {0, 1, …, 6}`. -/
theorem huckel_C7 (μ : ℝ) :
    (∃ v : Fin 7 → ℝ, v ≠ 0 ∧ C7 *ᵥ v = μ • v) ↔
      ∃ k : Fin 7, μ = 2 * Real.cos (2 * π * k / 7) := by
  have hone : ∀ v : Fin 7 → ℝ, (μ • (1 : Matrix (Fin 7) (Fin 7) ℝ)) *ᵥ v = μ • v := by
    intro v
    ext i
    simp [Matrix.mulVec, Matrix.one_apply, dotProduct, Finset.sum_ite_eq]
  have hstep : ∀ v : Fin 7 → ℝ,
      ((C7 - μ • (1 : Matrix (Fin 7) (Fin 7) ℝ)) *ᵥ v = 0) ↔ (C7 *ᵥ v = μ • v) := by
    intro v
    rw [Matrix.sub_mulVec, sub_eq_zero, hone]
  have h1 : (∃ v : Fin 7 → ℝ, v ≠ 0 ∧ C7 *ᵥ v = μ • v)
      ↔ (C7 - μ • (1 : Matrix (Fin 7) (Fin 7) ℝ)).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    exact exists_congr fun v => and_congr_right fun _ => (hstep v).symm
  rw [h1, ← Complex.ofReal_eq_zero, real_det_eq, det_charpoly, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    refine ⟨k, ?_⟩
    have h2 : ((ev k : ℝ) : ℂ) = (μ : ℂ) := sub_eq_zero.mp hk
    have h3 : ev k = μ := Complex.ofReal_inj.mp h2
    rw [← h3, ev]
  · rintro ⟨k, hk⟩
    refine ⟨k, Finset.mem_univ _, ?_⟩
    rw [hk]
    simp [ev]

end Chem

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

