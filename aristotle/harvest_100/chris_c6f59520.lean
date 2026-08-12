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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open Polynomial Matrix

/-! ## The adjacency matrix of the cycle graph `C₉` -/

/-- The adjacency matrix of the cycle graph `C₉`, i.e. the Hückel matrix of the
cyclononatetraenyl π-system with `α = 0` and `β = 1`. -/
noncomputable def adjC9 : Matrix (Fin 9) (Fin 9) ℝ := (SimpleGraph.cycleGraph 9).adjMatrix ℝ

lemma cyc9_adj_iff (i j : Fin 9) :
    (SimpleGraph.cycleGraph 9).Adj i j ↔ (j = i + 1 ∨ j = i - 1) := by
  rw [SimpleGraph.cycleGraph_adj']
  have h1 : ((1 : Fin 9) : ℕ) = 1 := rfl
  rw [← h1, ← Fin.ext_iff, ← Fin.ext_iff]
  constructor
  · rintro (h | h)
    · right; rw [← h, sub_sub_cancel]
    · left; rw [← h, add_sub_cancel]
  · rintro (h | h)
    · right; rw [h, add_sub_cancel_left]
    · left; rw [h, sub_sub_cancel]

lemma adjC9_apply (i j : Fin 9) : adjC9 i j = if j = i + 1 ∨ j = i - 1 then 1 else 0 := by
  rw [adjC9, SimpleGraph.adjMatrix_apply]
  simp [cyc9_adj_iff]

lemma succ_ne_pred (i : Fin 9) : (i + 1 : Fin 9) ≠ i - 1 := by
  revert i; decide

/-! ## A primitive ninth root of unity -/

/-- A primitive ninth root of unity. -/
noncomputable def w9 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 9)

lemma w9_isPrimitiveRoot : IsPrimitiveRoot w9 9 := by
  simpa [w9] using Complex.isPrimitiveRoot_exp 9 (by norm_num)

lemma w9_pow_nine : w9 ^ 9 = 1 := w9_isPrimitiveRoot.pow_eq_one

/-- `w9 ^ m + (w9 ^ m)⁻¹ = 2 cos (2πm/9)`. -/
lemma w9_pow_add_inv (m : ℕ) :
    w9 ^ m + (w9 ^ m)⁻¹ = ((2 * Real.cos (2 * Real.pi * m / 9) : ℝ) : ℂ) := by
  have h : w9 ^ m = Complex.exp (((2 * Real.pi * m / 9 : ℝ) : ℂ) * Complex.I) := by
    rw [w9, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h, ← Complex.exp_neg]
  push_cast
  rw [Complex.cos, neg_mul]
  ring

/-- The key algebraic identity behind the eigenvalue computation: for a ninth root of unity `z`,
shifting the exponent up and down by one multiplies `z ^ i` by `z + z⁻¹`. -/
lemma pow_shift_identity {z : ℂ} (hz9 : z ^ 9 = 1) (i : Fin 9) :
    z ^ ((i + 1 : Fin 9) : ℕ) + z ^ ((i - 1 : Fin 9) : ℕ) = z ^ (i : ℕ) * (z + z⁻¹) := by
  have hz : z ≠ 0 := by
    intro h
    rw [h] at hz9
    simp at hz9
  have hinv : z⁻¹ = z ^ 8 := by
    field_simp
    linear_combination -hz9
  rw [hinv]
  fin_cases i <;> simp
  · linear_combination -hz9
  · linear_combination -z * hz9
  · linear_combination -z ^ 2 * hz9
  · linear_combination -z ^ 3 * hz9
  · linear_combination -z ^ 4 * hz9
  · linear_combination -z ^ 5 * hz9
  · linear_combination -z ^ 6 * hz9
  · linear_combination -(1 + z ^ 7) * hz9

/-! ## Diagonalisation over `ℂ` -/

/-- The complexified adjacency matrix. -/
noncomputable def adjC9C : Matrix (Fin 9) (Fin 9) ℂ := adjC9.map Complex.ofRealHom

lemma adjC9C_apply (i j : Fin 9) : adjC9C i j = if j = i + 1 ∨ j = i - 1 then 1 else 0 := by
  rw [adjC9C, Matrix.map_apply, adjC9_apply]
  split_ifs <;> simp

/-- The discrete Fourier (Vandermonde) matrix built from the powers of `w9`. -/
noncomputable def fourier9 : Matrix (Fin 9) (Fin 9) ℂ :=
  Matrix.vandermonde (fun i : Fin 9 => w9 ^ (i : ℕ))

/-- The diagonal matrix of Hückel eigenvalues. -/
noncomputable def diagC9 : Matrix (Fin 9) (Fin 9) ℂ :=
  Matrix.diagonal (fun k : Fin 9 => ((2 * Real.cos (2 * Real.pi * k / 9) : ℝ) : ℂ))

/-- Multiplying a "Fourier column" by the adjacency matrix shifts the index up and down. -/
lemma adjC9C_row_sum (i : Fin 9) (z : ℂ) :
    ∑ j : Fin 9, adjC9C i j * z ^ (j : ℕ)
      = z ^ ((i + 1 : Fin 9) : ℕ) + z ^ ((i - 1 : Fin 9) : ℕ) := by
  have hne : (i + 1 : Fin 9) ≠ i - 1 := succ_ne_pred i
  have key : ∀ j : Fin 9, adjC9C i j * z ^ (j : ℕ)
      = (if j = i + 1 then z ^ ((i + 1 : Fin 9) : ℕ) else 0)
        + (if j = i - 1 then z ^ ((i - 1 : Fin 9) : ℕ) else 0) := by
    intro j
    rw [adjC9C_apply]
    by_cases h1 : j = i + 1
    · subst h1; simp [hne]
    · by_cases h2 : j = i - 1
      · subst h2; simp [h1]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (i + 1 : Fin 9) (fun _ => z ^ ((i + 1 : Fin 9) : ℕ)),
    Finset.sum_ite_eq' Finset.univ (i - 1 : Fin 9) (fun _ => z ^ ((i - 1 : Fin 9) : ℕ))]
  simp

lemma adjC9C_mul_fourier9 : adjC9C * fourier9 = fourier9 * diagC9 := by
  ext i k
  have hz9 : (w9 ^ (k : ℕ)) ^ 9 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, w9_pow_nine, one_pow]
  have hcol : ∀ j : Fin 9, fourier9 j k = (w9 ^ (k : ℕ)) ^ (j : ℕ) := by
    intro j
    rw [fourier9, Matrix.vandermonde_apply, ← pow_mul, ← pow_mul, mul_comm]
  rw [Matrix.mul_apply, diagC9, Matrix.mul_diagonal]
  calc ∑ j : Fin 9, adjC9C i j * fourier9 j k
      = ∑ j : Fin 9, adjC9C i j * (w9 ^ (k : ℕ)) ^ (j : ℕ) := by
        exact Finset.sum_congr rfl (fun j _ => by rw [hcol j])
    _ = (w9 ^ (k : ℕ)) ^ ((i + 1 : Fin 9) : ℕ) + (w9 ^ (k : ℕ)) ^ ((i - 1 : Fin 9) : ℕ) :=
        adjC9C_row_sum i _
    _ = (w9 ^ (k : ℕ)) ^ (i : ℕ) * (w9 ^ (k : ℕ) + (w9 ^ (k : ℕ))⁻¹) :=
        pow_shift_identity hz9 i
    _ = fourier9 i k * ((2 * Real.cos (2 * Real.pi * k / 9) : ℝ) : ℂ) := by
        rw [hcol i, w9_pow_add_inv]

lemma fourier9_det_ne_zero : (fourier9).det ≠ 0 := by
  rw [fourier9, Matrix.det_vandermonde_ne_zero_iff]
  intro i j hij
  exact Fin.ext (w9_isPrimitiveRoot.pow_inj i.isLt j.isLt hij)

lemma charpoly_adjC9C : adjC9C.charpoly = diagC9.charpoly := by
  have hdet : IsUnit (fourier9.det) := isUnit_iff_ne_zero.mpr fourier9_det_ne_zero
  have h1 : fourier9⁻¹ * (adjC9C * fourier9) = diagC9 := by
    rw [adjC9C_mul_fourier9, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  calc adjC9C.charpoly
      = (adjC9C * (fourier9 * fourier9⁻¹)).charpoly := by
        rw [Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
    _ = ((adjC9C * fourier9) * fourier9⁻¹).charpoly := by rw [Matrix.mul_assoc]
    _ = (fourier9⁻¹ * (adjC9C * fourier9)).charpoly := Matrix.charpoly_mul_comm _ _
    _ = diagC9.charpoly := by rw [h1]

/-! ## The main theorem -/

/-- **Hückel theory for C₉.** The characteristic polynomial of the adjacency matrix of the
cycle graph `C₉` is `∏ k, (X - 2 cos (2πk/9))`; equivalently, the adjacency eigenvalues of
`C₉`, listed with multiplicity, are `2 cos (2πk/9)` for `k = 0, …, 8`. -/
theorem huckel_C9 :
    adjC9.charpoly = ∏ k : Fin 9, (X - C (2 * Real.cos (2 * Real.pi * k / 9))) := by
  have hmap : (adjC9.charpoly).map (Complex.ofRealHom : ℝ →+* ℂ)
      = (∏ k : Fin 9, (X - C (2 * Real.cos (2 * Real.pi * k / 9)))).map
          (Complex.ofRealHom : ℝ →+* ℂ) := by
    rw [← Matrix.charpoly_map adjC9 Complex.ofRealHom, ← adjC9C, charpoly_adjC9C, diagC9,
      Matrix.charpoly_diagonal, Polynomial.map_prod]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    simp
  exact Polynomial.map_injective (Complex.ofRealHom : ℝ →+* ℂ) Complex.ofReal_injective hmap

/-- The set of adjacency eigenvalues of `C₉` is exactly `{2 cos (2πk/9) : k = 0, …, 8}`. -/
theorem spectrum_adjC9 :
    spectrum ℝ adjC9 = Set.range (fun k : Fin 9 => 2 * Real.cos (2 * Real.pi * k / 9)) := by
  ext r
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot, huckel_C9]
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, Set.mem_range]
  exact exists_congr (fun _ => by constructor <;> intro h <;> linarith)

end Chem

