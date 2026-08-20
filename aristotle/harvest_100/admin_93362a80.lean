/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial Matrix SimpleGraph

/-! ### A primitive 7th root of unity -/

/-- A primitive 7th root of unity. -/
noncomputable def w7 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 7)

lemma w7_primitive : IsPrimitiveRoot w7 7 := Complex.isPrimitiveRoot_exp 7 (by norm_num)

lemma w7_pow_seven : w7 ^ 7 = 1 := w7_primitive.pow_eq_one

/-- Powers of `w7` only depend on the exponent modulo `7`. -/
lemma w7_pow_congr {a b : ℕ} (h : a % 7 = b % 7) : w7 ^ a = w7 ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 7, pow_add, pow_mul, w7_pow_seven, one_pow, one_mul, h]
  conv_rhs => rw [← Nat.div_add_mod b 7, pow_add, pow_mul, w7_pow_seven, one_pow, one_mul]

/-! ### The discrete Fourier (Vandermonde) matrix -/

/-- The discrete Fourier matrix of order 7, i.e. the Vandermonde matrix on the powers of `w7`. -/
noncomputable def dft7 : Matrix (Fin 7) (Fin 7) ℂ :=
  Matrix.vandermonde (fun i : Fin 7 => w7 ^ (i : ℕ))

lemma dft7_apply (i k : Fin 7) : dft7 i k = w7 ^ ((i : ℕ) * (k : ℕ)) := by
  simp [dft7, Matrix.vandermonde_apply, ← pow_mul]

lemma dft7_det_ne_zero : dft7.det ≠ 0 := by
  refine Matrix.det_vandermonde_ne_zero_iff.mpr ?_
  intro i j h
  exact Fin.ext (w7_primitive.pow_inj i.isLt j.isLt h)

lemma dft7_shift (a i k : Fin 7) : dft7 (i + a) k = w7 ^ ((i : ℕ) * (k : ℕ) + (a : ℕ) * (k : ℕ)) := by
  rw [dft7_apply]
  refine w7_pow_congr ?_
  have hv : ((i + a : Fin 7) : ℕ) = ((i : ℕ) + (a : ℕ)) % 7 := by simp [Fin.val_add]
  rw [hv]
  have h : ((((i : ℕ) + (a : ℕ)) % 7) * (k : ℕ)) % 7 = (((i : ℕ) + (a : ℕ)) * (k : ℕ)) % 7 :=
    (Nat.mod_modEq _ 7).mul_right _
  rw [h]
  congr 1
  ring

/-! ### The adjacency matrix of `C₇` acting on a vector -/

lemma cyc7_filter (i : Fin 7) :
    Finset.univ.filter (fun j => (cycleGraph 7).Adj i j) = {i - 1, i + 1} := by
  revert i; decide

lemma cyc7_ne (i : Fin 7) : (i - 1) ≠ (i + 1) := by revert i; decide

lemma cyc7_sub_one (i : Fin 7) : i - 1 = i + 6 := by revert i; decide

lemma adj_mul_row (i : Fin 7) (f : Fin 7 → ℂ) :
    ∑ j, ((cycleGraph 7).adjMatrix ℂ) i j * f j = f (i - 1) + f (i + 1) := by
  have h1 : ∀ j, ((cycleGraph 7).adjMatrix ℂ) i j * f j
      = if (cycleGraph 7).Adj i j then f j else 0 := by
    intro j; simp [SimpleGraph.adjMatrix_apply]
  simp only [h1, ← Finset.sum_filter, cyc7_filter i]
  rw [Finset.sum_pair (cyc7_ne i)]

/-! ### Diagonalisation -/

/-- The `k`-th Hückel eigenvalue, written in terms of the root of unity `w7`. -/
noncomputable def lam7 (k : Fin 7) : ℂ := w7 ^ (k : ℕ) + w7 ^ (6 * (k : ℕ))

lemma adj_mul_dft7 :
    ((cycleGraph 7).adjMatrix ℂ) * dft7 = dft7 * Matrix.diagonal lam7 := by
  ext i k
  rw [Matrix.mul_apply, adj_mul_row i (fun j => dft7 j k), Matrix.mul_diagonal,
    cyc7_sub_one, dft7_shift, dft7_shift, dft7_apply, lam7]
  norm_num [pow_add, mul_add]
  ring

lemma charpoly_complex :
    ((cycleGraph 7).adjMatrix ℂ).charpoly = ∏ k : Fin 7, (X - C (lam7 k)) := by
  have hdet : IsUnit dft7.det := isUnit_iff_ne_zero.mpr dft7_det_ne_zero
  have key : ((cycleGraph 7).adjMatrix ℂ)
      = (Matrix.nonsingInvUnit dft7 hdet).val * (Matrix.diagonal lam7)
        * (Matrix.nonsingInvUnit dft7 hdet)⁻¹.val := by
    show _ = dft7 * Matrix.diagonal lam7 * dft7⁻¹
    rw [← adj_mul_dft7, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  rw [key, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]

lemma lam7_eq (k : Fin 7) :
    lam7 k = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 7) : ℝ) : ℂ) := by
  set t : ℝ := 2 * Real.pi * (k : ℕ) / 7 with ht
  have h1 : w7 ^ (k : ℕ) = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [w7, ← Complex.exp_nat_mul]
    congr 1
    rw [ht]
    push_cast
    ring
  have hmul : w7 ^ (6 * (k : ℕ)) * w7 ^ (k : ℕ) = 1 := by
    rw [← pow_add, show 6 * (k : ℕ) + (k : ℕ) = 7 * (k : ℕ) by ring, pow_mul, w7_pow_seven,
      one_pow]
  have h2 : w7 ^ (6 * (k : ℕ)) = Complex.exp (-((t : ℂ) * Complex.I)) := by
    rw [Complex.exp_neg, ← h1]
    exact eq_inv_of_mul_eq_one_left hmul
  rw [lam7, h1, h2,
    show Complex.exp ((t : ℂ) * Complex.I) + Complex.exp (-((t : ℂ) * Complex.I))
      = 2 * Complex.cos (t : ℂ) by rw [Complex.cos]; ring_nf]
  push_cast
  rfl

lemma adjMatrix_map :
    ((cycleGraph 7).adjMatrix ℝ).map (Complex.ofRealHom : ℝ →+* ℂ)
      = (cycleGraph 7).adjMatrix ℂ := by
  ext i j
  by_cases h : (cycleGraph 7).Adj i j <;>
    simp [Matrix.map_apply, SimpleGraph.adjMatrix_apply, h]

/-- The characteristic polynomial of the adjacency matrix of the cycle graph `C₇`
splits with roots `2 cos (2πk/7)` for `k = 0, …, 6`: these are the Hückel (adjacency)
eigenvalues of `C₇`, listed with multiplicity. -/
theorem huckel_C7 :
    ((cycleGraph 7).adjMatrix ℝ).charpoly
      = ∏ k ∈ Finset.range 7, (X - C (2 * Real.cos (2 * Real.pi * k / 7))) := by
  have hinj : Function.Injective (Polynomial.map (Complex.ofRealHom : ℝ →+* ℂ)) :=
    Polynomial.map_injective _ Complex.ofReal_injective
  apply hinj
  rw [← Matrix.charpoly_map, adjMatrix_map, charpoly_complex]
  rw [Polynomial.map_prod, ← Fin.prod_univ_eq_prod_range
    (fun k : ℕ => Polynomial.map (Complex.ofRealHom : ℝ →+* ℂ)
      (X - C (2 * Real.cos (2 * Real.pi * k / 7)))) 7]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [lam7_eq k]
  simp

/-- Consequently each of the seven numbers `2 cos (2πk/7)`, `k = 0, …, 6`, is an eigenvalue
of the adjacency matrix of `C₇` (a root of its characteristic polynomial). -/
theorem huckel_C7_isRoot {k : ℕ} (hk : k < 7) :
    ((cycleGraph 7).adjMatrix ℝ).charpoly.IsRoot (2 * Real.cos (2 * Real.pi * k / 7)) := by
  rw [Polynomial.IsRoot, huckel_C7, Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_range.mpr hk) ?_
  simp

end Chem

