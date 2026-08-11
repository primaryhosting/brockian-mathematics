import Mathlib

/-!
# Hückel theory for the cycle C₉

The adjacency matrix of the cycle graph `C₉` is diagonalized by the discrete Fourier
(Vandermonde) matrix built from a primitive 9-th root of unity.  Consequently its
characteristic polynomial factors as `∏ k, (X - 2 cos (2πk/9))`, and its spectrum is
exactly `{2 cos (2πk/9) : k = 0, …, 8}` — the Hückel energy levels of a nine-membered
conjugated ring.
-/

open Polynomial Matrix SimpleGraph Complex

namespace Chem

/-- The adjacency matrix of the cycle graph `C₉`, over `ℂ`. -/
noncomputable def C9adj : Matrix (Fin 9) (Fin 9) ℂ := (SimpleGraph.cycleGraph 9).adjMatrix ℂ

/-- The `k`-th Hückel eigenvalue of `C₉`: `2 cos (2πk/9)`. -/
noncomputable def C9eigenvalue (k : Fin 9) : ℝ := 2 * Real.cos (2 * Real.pi * (k : ℕ) / 9)

/-- A primitive 9-th root of unity. -/
noncomputable def omega9 : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 9)

/-- The Fourier (Vandermonde) matrix diagonalizing the adjacency matrix of `C₉`. -/
noncomputable def F9 : Matrix (Fin 9) (Fin 9) ℂ :=
  Matrix.vandermonde (fun i : Fin 9 => omega9 ^ (i : ℕ))

theorem isPrimitiveRoot_omega9 : IsPrimitiveRoot omega9 9 := by
  simpa [omega9] using Complex.isPrimitiveRoot_exp 9 (by norm_num)

theorem omega9_pow_nine : omega9 ^ 9 = 1 := by
  rw [omega9, ← Complex.exp_nat_mul,
    show ((9 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 9) = 2 * (Real.pi : ℂ) * Complex.I by
      push_cast; ring]
  simp [Complex.exp_two_pi_mul_I]

theorem omega9_pow_pow_nine (k : Fin 9) : (omega9 ^ (k : ℕ)) ^ 9 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, omega9_pow_nine, one_pow]

theorem F9_apply (i k : Fin 9) : F9 i k = (omega9 ^ (k : ℕ)) ^ (i : ℕ) := by
  simp [F9, Matrix.vandermonde_apply, ← pow_mul, mul_comm]

/-- The combinatorial heart of the diagonalization: summing `x ^ j` over the neighbours `j`
of a vertex `i` of `C₉` gives `x ^ i * (x + x ^ 8)`, whenever `x ^ 9 = 1`. -/
theorem adj_sum_pow (x : ℂ) (hx9 : x ^ 9 = 1) (i : Fin 9) :
    (∑ j : Fin 9, (if (cycleGraph 9).Adj i j then x ^ (j : ℕ) else 0)) = x ^ (i : ℕ) * (x + x ^ 8) := by
  fin_cases i <;> simp +decide [Fin.sum_univ_succ]
  · linear_combination -hx9
  · linear_combination (-x) * hx9
  · linear_combination (-x ^ 2) * hx9
  · linear_combination (-x ^ 3) * hx9
  · linear_combination (-x ^ 4) * hx9
  · linear_combination (-x ^ 5) * hx9
  · linear_combination (-x ^ 6) * hx9
  · linear_combination (-(1 + x ^ 7)) * hx9

/-- `ω^k + ω^{-k} = 2 cos (2πk/9)`. -/
theorem omega9_add_pow_eight (k : Fin 9) :
    omega9 ^ (k : ℕ) + (omega9 ^ (k : ℕ)) ^ 8 = ((C9eigenvalue k : ℝ) : ℂ) := by
  have h8 : (omega9 ^ (k : ℕ)) ^ 8 = (omega9 ^ (k : ℕ))⁻¹ := by
    have hne : omega9 ≠ 0 := by simp [omega9, Complex.exp_ne_zero]
    field_simp
    linear_combination omega9_pow_pow_nine k
  have hk : omega9 ^ (k : ℕ) = Complex.exp ((2 * Real.pi * (k : ℕ) / 9 : ℝ) * Complex.I) := by
    rw [omega9, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h8, hk, ← Complex.exp_neg, C9eigenvalue]
  push_cast
  rw [Complex.two_cos]
  ring_nf

/-- The Fourier matrix diagonalizes the adjacency matrix of `C₉`. -/
theorem C9adj_mul_F9 :
    C9adj * F9 = F9 * Matrix.diagonal (fun k : Fin 9 => ((C9eigenvalue k : ℝ) : ℂ)) := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, F9_apply, C9adj,
    SimpleGraph.adjMatrix_apply, ← omega9_add_pow_eight, ite_mul, one_mul, zero_mul,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact adj_sum_pow _ (omega9_pow_pow_nine k) i

theorem F9_det_ne_zero : F9.det ≠ 0 := by
  rw [F9, Matrix.det_vandermonde_ne_zero_iff]
  intro i j h
  exact Fin.ext (isPrimitiveRoot_omega9.pow_inj i.isLt j.isLt h)

/-- Sanity check on the model: in `C₉` the neighbours of a vertex `i` are exactly `i + 1`
and `i - 1` (in `Fin 9`). -/
theorem cycleGraph_nine_adj_iff (i j : Fin 9) :
    (cycleGraph 9).Adj i j ↔ (j = i + 1 ∨ i = j + 1) := by
  revert i j
  decide

/-- The Fourier vector `i ↦ ω^{ki}` is an eigenvector of the adjacency matrix of `C₉`
with eigenvalue `2 cos (2πk/9)`. -/
theorem C9adj_mulVec_fourier (k : Fin 9) :
    C9adj *ᵥ (fun i : Fin 9 => (omega9 ^ (k : ℕ)) ^ (i : ℕ)) =
      ((C9eigenvalue k : ℝ) : ℂ) • (fun i : Fin 9 => (omega9 ^ (k : ℕ)) ^ (i : ℕ)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, C9adj, SimpleGraph.adjMatrix_apply, ite_mul,
    one_mul, zero_mul, Pi.smul_apply, smul_eq_mul, ← omega9_add_pow_eight]
  rw [adj_sum_pow _ (omega9_pow_pow_nine k) i, mul_comm]

/-- **Hückel theory for C₉ (characteristic polynomial form).**  The characteristic polynomial
of the adjacency matrix of the cycle `C₉` is `∏_{k=0}^{8} (X - 2 cos (2πk/9))`. -/
theorem huckel_C9_charpoly :
    C9adj.charpoly = ∏ k : Fin 9, (X - Polynomial.C ((C9eigenvalue k : ℝ) : ℂ)) := by
  set D : Matrix (Fin 9) (Fin 9) ℂ :=
    Matrix.diagonal (fun k : Fin 9 => ((C9eigenvalue k : ℝ) : ℂ)) with hD
  have hdet : IsUnit F9.det := isUnit_iff_ne_zero.2 F9_det_ne_zero
  set U : (Matrix (Fin 9) (Fin 9) ℂ)ˣ := Matrix.nonsingInvUnit F9 hdet with hU
  have hUval : (U : Matrix (Fin 9) (Fin 9) ℂ) = F9 := rfl
  have hUinv : ((U⁻¹ : (Matrix (Fin 9) (Fin 9) ℂ)ˣ) : Matrix (Fin 9) (Fin 9) ℂ) = F9⁻¹ := rfl
  have hconj : C9adj = (U : Matrix (Fin 9) (Fin 9) ℂ) * D * (U⁻¹ : (Matrix (Fin 9) (Fin 9) ℂ)ˣ) := by
    rw [hUval, hUinv, ← C9adj_mul_F9, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]
  rw [hconj, Matrix.charpoly_units_conj, hD, Matrix.charpoly_diagonal]

/-- **Hückel theory for C₉.**  The eigenvalues (spectrum) of the adjacency matrix of the
cycle graph `C₉` are exactly the nine numbers `2 cos (2πk/9)`, `k = 0, …, 8`. -/
theorem huckel_C9 :
    spectrum ℂ C9adj = Set.range (fun k : Fin 9 => ((C9eigenvalue k : ℝ) : ℂ)) := by
  ext r
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C9_charpoly, Polynomial.IsRoot.def,
    Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [Finset.prod_eq_zero_iff]
  simp [sub_eq_zero, eq_comm]

end Chem

import Mathlib
import RequestProject.Huckel

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

