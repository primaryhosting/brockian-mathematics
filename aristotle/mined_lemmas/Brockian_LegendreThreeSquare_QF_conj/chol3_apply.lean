import Mathlib

/-!
# Legendre's three-square theorem

A natural number `n` is a sum of three squares if and only if it is not of the
form `4 ^ a * (8 * b + 7)`.

The proof is self-contained (only core `Mathlib` is used).  The hard direction
goes through the classical route:

* Minkowski's convex body theorem shows that every positive definite integral
  ternary quadratic form of determinant one represents `1`, hence (by descent)
  is of the shape `Nᵀ * N`.
* Dirichlet's theorem on primes in arithmetic progressions together with
  quadratic reciprocity produces, for every `n` with `n % 4 ≠ 0` and
  `n % 8 ≠ 7`, an integer `m > 0` with `n ∣ m + 1` and `-n` a square modulo `m`.
  Out of these data one builds an explicit positive definite integral ternary
  form of determinant one whose `(0,0)` entry is `n`.
-/

namespace Brockian.LegendreThreeSquare

open Matrix MeasureTheory
open scoped ENNReal

/-! ## Integral quadratic forms -/

/-- The value at `v` of the quadratic form attached to the integer matrix `A`. -/

lemma chol3_apply (A : Matrix (Fin 3) (Fin 3) ℤ) (hsym : A.IsSymm) (h00 : 0 < A 0 0)
    (hd2 : 0 < A 0 0 * A 1 1 - A 0 1 ^ 2) (hdet : A.det = 1) (v : Fin 3 → ℤ) :
    ((QF A v : ℤ) : ℝ) = ∑ i, ((chol3Mat A).mulVec (fun j => (v j : ℝ)) i) ^ 2 := by
  have ha : (0 : ℝ) < (A 0 0 : ℝ) := by exact_mod_cast h00
  have hd : (0 : ℝ) < ((A 0 0 * A 1 1 - A 0 1 ^ 2 : ℤ) : ℝ) := by exact_mod_cast hd2
  have h10 : A 1 0 = A 0 1 := by have := congr_fun (congr_fun hsym 1) 0; simpa using this.symm
  have h20 : A 2 0 = A 0 2 := by have := congr_fun (congr_fun hsym 2) 0; simpa using this.symm
  have h21 : A 2 1 = A 1 2 := by have := congr_fun (congr_fun hsym 2) 1; simpa using this.symm
  have hdetR : (A 0 0 : ℝ) * (A 1 1 : ℝ) * (A 2 2 : ℝ)
      + 2 * (A 0 1 : ℝ) * (A 0 2 : ℝ) * (A 1 2 : ℝ) - (A 0 0 : ℝ) * (A 1 2 : ℝ) ^ 2
      - (A 1 1 : ℝ) * (A 0 2 : ℝ) ^ 2 - (A 2 2 : ℝ) * (A 0 1 : ℝ) ^ 2 = 1 := by
    have hh : A.det = 1 := hdet
    rw [Matrix.det_fin_three] at hh
    have h2 : A 0 0 * A 1 1 * A 2 2 + 2 * A 0 1 * A 0 2 * A 1 2
        - A 0 0 * A 1 2 ^ 2 - A 1 1 * A 0 2 ^ 2 - A 2 2 * A 0 1 ^ 2 = 1 := by
      rw [h10, h20, h21] at hh; linarith [hh]
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h2
  simp only [QF, chol3Mat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.cons_val_two,
    Matrix.tail_cons]
  rw [Real.sqrt_div hd.le, Real.sqrt_mul ha.le]
  push_cast [h10, h20, h21]
  set sa := Real.sqrt (A 0 0 : ℝ) with hsadef
  set sd := Real.sqrt ((A 0 0 : ℝ) * (A 1 1 : ℝ) - (A 0 1 : ℝ) ^ 2) with hsddef
  have hsa2 : sa ^ 2 = (A 0 0 : ℝ) := Real.sq_sqrt ha.le
  have hdpos : (0 : ℝ) < (A 0 0 : ℝ) * (A 1 1 : ℝ) - (A 0 1 : ℝ) ^ 2 := by push_cast at hd; linarith
  have hsd2 : sd ^ 2 = (A 0 0 : ℝ) * (A 1 1 : ℝ) - (A 0 1 : ℝ) ^ 2 := Real.sq_sqrt hdpos.le
  have hsa4 : sa ^ 4 = (A 0 0 : ℝ) ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsa2]
  have hsd4 : sd ^ 4 = ((A 0 0 : ℝ) * (A 1 1 : ℝ) - (A 0 1 : ℝ) ^ 2) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsd2]
  have hsa : sa ≠ 0 := by rw [hsadef]; positivity
  have hsd : sd ≠ 0 := by rw [hsddef]; positivity
  field_simp
  ring_nf
  rw [hsa4, hsd4, hsa2, hsd2]
  ring_nf
  linear_combination ((A 0 0 : ℝ) * (v 2 : ℝ) ^ 2) * hdetR

/-! ## Leading minors of a positive definite integral form -/

