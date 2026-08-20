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

set_option grind.warning false

/-!
# Hückel spectrum of the cycle `C₁₅`

The adjacency matrix of the cycle graph `C₁₅` has characteristic polynomial
`∏_{k=0}^{14} (X - 2cos(2πk/15))`; equivalently its eigenvalues are the numbers
`2cos(2πk/15)` for `k = 0, …, 14`.
-/

namespace Chem

open Matrix Polynomial Complex

/-- A primitive 15-th root of unity. -/

noncomputable def w : ℂ := Complex.exp (2 * Real.pi * Complex.I / 15)

/-- The Hückel (adjacency) matrix of the cycle `C₁₅`. -/

noncomputable def A : Matrix (Fin 15) (Fin 15) ℂ := (SimpleGraph.cycleGraph 15).adjMatrix ℂ

/-- The list of Hückel eigenvalues of `C₁₅`. -/

noncomputable def hlevel (k : ℕ) : ℂ := ((2 * Real.cos (2 * Real.pi * k / 15) : ℝ) : ℂ)

/-- The diagonal matrix of eigenvalues. -/

noncomputable def D : Matrix (Fin 15) (Fin 15) ℂ := Matrix.diagonal fun k => hlevel k.val

/-- The (Vandermonde / discrete Fourier) matrix of eigenvectors. -/

noncomputable def F : Matrix (Fin 15) (Fin 15) ℂ := Matrix.vandermonde fun j : Fin 15 => w ^ j.val

theorem w_primitive : IsPrimitiveRoot w 15 := by
  have := Complex.isPrimitiveRoot_exp 15 (by norm_num)
  simpa [w, mul_comm, mul_assoc, mul_left_comm] using this

theorem w_pow_15 : w ^ (15 : ℕ) = 1 := w_primitive.pow_eq_one

theorem w_ne_zero : w ≠ 0 := by
  intro h
  have := w_pow_15
  rw [h] at this
  norm_num at this

theorem w_pow_congr {a b : ℕ} (h : a % 15 = b % 15) : w ^ a = w ^ b := by
  have key : ∀ m : ℕ, w ^ m = w ^ (m % 15) := by
    intro m
    conv_lhs => rw [← Nat.div_add_mod m 15]
    rw [pow_add, pow_mul, w_pow_15, one_pow, one_mul]
  rw [key a, key b, h]

theorem exp_add_inv (t : ℝ) :
    Complex.exp ((t : ℂ) * Complex.I) + (Complex.exp ((t : ℂ) * Complex.I))⁻¹
      = ((2 * Real.cos t : ℝ) : ℂ) := by
  rw [← Complex.exp_neg]
  have h1 : -((t : ℂ) * Complex.I) = ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h1, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  simp [Complex.cos_neg, Complex.sin_neg]
  ring

theorem w_pow_eq_exp (k : ℕ) :
    w ^ k = Complex.exp (((2 * Real.pi * k / 15 : ℝ) : ℂ) * Complex.I) := by
  rw [w, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem w_pow_add_inv (k : ℕ) : w ^ k + (w ^ k)⁻¹ = hlevel k := by
  rw [w_pow_eq_exp, exp_add_inv, hlevel]

theorem F_apply (i k : Fin 15) : F i k = (w ^ i.val) ^ k.val := rfl

theorem A_mul_F : A * F = F * D := by
  ext i k
  rw [A, SimpleGraph.adjMatrix_mul_apply, SimpleGraph.cycleGraph_neighborFinset]
  have hne : (i - 1 : Fin 15) ≠ i + 1 := by
    intro h
    have h1 : (i - 1 : Fin 15) + 1 = (i + 1) + 1 := by rw [h]
    rw [sub_add_cancel, add_assoc] at h1
    simp at h1
  rw [Finset.sum_pair hne]
  -- compute the two neighbouring entries
  have key : ∀ a : Fin 15, (a + 1 : Fin 15).val = (a.val + 1) % 15 := by
    intro a; rw [Fin.val_add]; rfl
  have hplus : w ^ ((i + 1 : Fin 15)).val = w ^ i.val * w := by
    rw [← pow_succ]
    apply w_pow_congr
    rw [key i]
    omega
  have hminus : w ^ ((i - 1 : Fin 15)).val * w = w ^ i.val := by
    rw [← pow_succ]
    apply w_pow_congr
    rw [← key (i - 1), sub_add_cancel]
    omega
  have hminus' : w ^ ((i - 1 : Fin 15)).val = w ^ i.val * w⁻¹ := by
    field_simp [w_ne_zero] at hminus ⊢
    linear_combination hminus
  simp only [D, Matrix.mul_diagonal, F_apply]
  rw [hplus, hminus', mul_pow, mul_pow, ← w_pow_add_inv k.val, inv_pow]
  ring

theorem F_isUnit : IsUnit F := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, F, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_
  simp only [Finset.mem_Ioi] at hj
  refine sub_ne_zero_of_ne fun h => ?_
  have := w_primitive.pow_inj j.isLt i.isLt h
  exact absurd (Fin.ext this) (Fin.ne_of_gt hj)

theorem A_eq_conj : A = (F_isUnit.unit : Matrix (Fin 15) (Fin 15) ℂ) * D
    * ((F_isUnit.unit⁻¹ : (Matrix (Fin 15) (Fin 15) ℂ)ˣ) : Matrix (Fin 15) (Fin 15) ℂ) := by
  have hu : (F_isUnit.unit : Matrix (Fin 15) (Fin 15) ℂ) = F := F_isUnit.unit_spec
  calc A = A * ((F_isUnit.unit : Matrix (Fin 15) (Fin 15) ℂ)
            * ((F_isUnit.unit⁻¹ : (Matrix (Fin 15) (Fin 15) ℂ)ˣ) :
              Matrix (Fin 15) (Fin 15) ℂ)) := by rw [Units.mul_inv, mul_one]
    _ = (A * F) * ((F_isUnit.unit⁻¹ : (Matrix (Fin 15) (Fin 15) ℂ)ˣ) :
            Matrix (Fin 15) (Fin 15) ℂ) := by rw [← mul_assoc, hu]
    _ = (F * D) * ((F_isUnit.unit⁻¹ : (Matrix (Fin 15) (Fin 15) ℂ)ˣ) :
            Matrix (Fin 15) (Fin 15) ℂ) := by rw [A_mul_F]
    _ = _ := by rw [hu]

theorem charpoly_A : A.charpoly = ∏ k : Fin 15, (X - C (hlevel k.val)) := by
  rw [A_eq_conj, Matrix.charpoly_units_conj, D, Matrix.charpoly_diagonal]

/-- **Hückel theory for the annulene `C₁₅`.**  The characteristic polynomial of the adjacency
matrix of the cycle graph `C₁₅` is `∏_{k=0}^{14} (X - 2·cos(2πk/15))`, i.e. the adjacency
eigenvalues of `C₁₅` are exactly `2·cos(2πk/15)` for `k = 0, …, 14` (with multiplicity). -/

theorem huckel_C15 :
    ((SimpleGraph.cycleGraph 15).adjMatrix ℂ).charpoly =
      ∏ k ∈ Finset.range 15,
        (X - C ((2 * Real.cos (2 * Real.pi * k / 15) : ℝ) : ℂ)) := by
  have := charpoly_A
  rw [A] at this
  rw [this, Fin.prod_univ_eq_prod_range (fun k : ℕ => (X - C (hlevel k)))]
  rfl

/-- The spectrum (set of eigenvalues) of the adjacency matrix of `C₁₅` is
`{2·cos(2πk/15) : k = 0, …, 14}`. -/
