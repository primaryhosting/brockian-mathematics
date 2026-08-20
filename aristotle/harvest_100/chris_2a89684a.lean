/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Chem

open Polynomial Matrix Complex

/-- A primitive 10-th root of unity. -/
noncomputable def w : ℂ := Complex.exp (2 * Real.pi * Complex.I / 10)

/-- The adjacency matrix of the cycle graph `C₁₀`; this is the Hückel matrix of
cyclodecapentaene in units where the Coulomb integral `α` is `0` and the resonance
integral `β` is `1`. -/
noncomputable def A10 : Matrix (Fin 10) (Fin 10) ℂ :=
  (SimpleGraph.cycleGraph 10).adjMatrix ℂ

/-- The Hückel eigenvalue `2 cos (2πk/10)`. -/
noncomputable def huckelEigenvalue (k : Fin 10) : ℝ :=
  2 * Real.cos (2 * Real.pi * (k : ℕ) / 10)

/-- The (Vandermonde / discrete Fourier) matrix diagonalizing `A10`. -/
noncomputable def U10 : Matrix (Fin 10) (Fin 10) ℂ :=
  Matrix.vandermonde (fun i : Fin 10 => w ^ (i : ℕ))

/-- The diagonal matrix of Hückel eigenvalues. -/
noncomputable def D10 : Matrix (Fin 10) (Fin 10) ℂ :=
  Matrix.diagonal (fun k : Fin 10 => (huckelEigenvalue k : ℂ))

lemma w_pow_ten : w ^ (10 : ℕ) = 1 := by
  rw [w, ← Complex.exp_nat_mul,
    show ((10 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 10) = 2 * Real.pi * Complex.I by
      push_cast; ring]
  exact Complex.exp_two_pi_mul_I

lemma w_pow_add_inv (k : Fin 10) :
    w ^ (k : ℕ) + (w ^ (k : ℕ))⁻¹ = (huckelEigenvalue k : ℂ) := by
  have h : w ^ (k : ℕ) = Complex.exp ((2 * Real.pi * (k : ℕ) / 10 : ℝ) * Complex.I) := by
    rw [w, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  rw [h, ← Complex.exp_neg, ← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I, huckelEigenvalue]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

/-- Expansion of one row of the adjacency matrix of `C₁₀` against the geometric vector
`j ↦ z ^ j`, for `z` a 10-th root of unity. -/
lemma cycle_row (z : ℂ) (h10 : z ^ (10 : ℕ) = 1) (i : Fin 10) :
    ∑ j : Fin 10, (if (SimpleGraph.cycleGraph 10).Adj i j then (1 : ℂ) else 0) * z ^ (j : ℕ)
      = z ^ (i : ℕ) * (z + z ^ 9) := by
  fin_cases i <;> simp +decide [Fin.sum_univ_succ]
  all_goals
    first
      | ring1
      | linear_combination (-1 : ℂ) * h10
      | linear_combination (-z) * h10
      | linear_combination (-z ^ 2) * h10
      | linear_combination (-z ^ 3) * h10
      | linear_combination (-z ^ 4) * h10
      | linear_combination (-z ^ 5) * h10
      | linear_combination (-z ^ 6) * h10
      | linear_combination (-z ^ 7) * h10
      | linear_combination (-(1 + z ^ 8)) * h10

lemma A10_mul_U10 : A10 * U10 = U10 * D10 := by
  ext i k
  have hz10 : (w ^ (k : ℕ)) ^ (10 : ℕ) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, w_pow_ten, one_pow]
  have hinv : (w ^ (k : ℕ))⁻¹ = (w ^ (k : ℕ)) ^ 9 :=
    inv_eq_of_mul_eq_one_left (by rw [← pow_succ]; exact hz10)
  have hcomm : ∀ j : ℕ, (w ^ j) ^ (k : ℕ) = (w ^ (k : ℕ)) ^ j := fun j => by
    rw [← pow_mul, ← pow_mul, mul_comm]
  rw [Matrix.mul_apply, D10, Matrix.mul_diagonal, ← w_pow_add_inv k, hinv, U10,
    Matrix.vandermonde_apply, hcomm]
  rw [← cycle_row (w ^ (k : ℕ)) hz10 i]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [A10, SimpleGraph.adjMatrix_apply, Matrix.vandermonde_apply, hcomm]

lemma det_U10_ne_zero : (U10).det ≠ 0 := by
  have hprim : IsPrimitiveRoot w 10 := by
    have := Complex.isPrimitiveRoot_exp 10 (by norm_num)
    simpa [w] using this
  refine Matrix.det_vandermonde_ne_zero_iff.mpr ?_
  intro i j hij
  exact Fin.ext (hprim.pow_inj i.isLt j.isLt hij)

lemma charpoly_A10 :
    A10.charpoly = ∏ k : Fin 10, (X - C ((huckelEigenvalue k : ℂ))) := by
  have hU : IsUnit U10.det := isUnit_iff_ne_zero.mpr det_U10_ne_zero
  have key : A10 = (U10.nonsingInvUnit hU).val * D10 * ((U10.nonsingInvUnit hU)⁻¹).val := by
    show A10 = U10 * D10 * U10⁻¹
    rw [← A10_mul_U10, mul_assoc, Matrix.mul_nonsing_inv _ hU, mul_one]
  rw [key, Matrix.charpoly_units_conj, D10, Matrix.charpoly_diagonal]

/-- **Hückel theory for C₁₀.**  The characteristic polynomial of the adjacency matrix of the
cycle graph `C₁₀` factors as `∏ k, (X - 2 cos (2πk/10))`; consequently the eigenvalues
(spectrum) of that matrix are exactly the numbers `2 cos (2πk/10)`, `k = 0, …, 9`. -/
theorem huckel_C10 :
    ((SimpleGraph.cycleGraph 10).adjMatrix ℂ).charpoly
        = ∏ k : Fin 10, (X - C ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 10) : ℝ) : ℂ)) ∧
      ∀ μ : ℂ, μ ∈ spectrum ℂ ((SimpleGraph.cycleGraph 10).adjMatrix ℂ) ↔
        ∃ k : Fin 10, μ = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 10) : ℝ) : ℂ) := by
  have hchar := charpoly_A10
  rw [A10] at hchar
  refine ⟨hchar, fun μ => ?_⟩
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot, hchar,
    Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, huckelEigenvalue]
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    exact ⟨k, sub_eq_zero.mp hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Finset.mem_univ k, sub_eq_zero.mpr hk⟩

end Chem

