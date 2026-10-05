import Mathlib
/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Polynomial

namespace Chem

/-- A primitive 8-th root of unity. -/
noncomputable def zeta8 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)

/-- The adjacency matrix of the cycle graph `C₈`: vertices are `Fin 8` with cyclic
arithmetic, and `i` is adjacent to `i + 1` and `i - 1`. -/
def C8adj : Matrix (Fin 8) (Fin 8) ℂ :=
  fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

/-- The `k`-th Hückel eigenvalue of `C₈`, namely `2 cos (2πk/8)`. -/
noncomputable def C8eigen (k : Fin 8) : ℂ := 2 * Real.cos (2 * Real.pi * k / 8)

/-- The discrete Fourier transform matrix, whose columns are the eigenvectors of `C8adj`. -/
noncomputable def C8dft : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.vandermonde (fun j : Fin 8 => zeta8 ^ (j : ℕ))

lemma zeta8_prim : IsPrimitiveRoot zeta8 8 := by
  simpa [zeta8] using Complex.isPrimitiveRoot_exp 8 (by norm_num)

lemma zeta8_pow_eight : zeta8 ^ 8 = 1 := zeta8_prim.pow_eq_one

lemma zeta8_pow_eq (m : ℕ) :
    zeta8 ^ m = Complex.exp ((2 * Real.pi * m / 8 : ℝ) * Complex.I) := by
  rw [zeta8, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma exp_add_inv (x : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) + (Complex.exp ((x : ℂ) * Complex.I))⁻¹
      = 2 * (Real.cos x : ℂ) := by
  rw [← Complex.exp_neg, ← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I,
    show ((-(x : ℂ))) = ((-x : ℝ) : ℂ) by push_cast; ring]
  simp [Complex.ofReal_cos]
  ring

/-- The `k`-th eigenvalue expressed via the root of unity. -/
lemma C8eigen_eq (k : Fin 8) :
    C8eigen k = zeta8 ^ (k : ℕ) + (zeta8 ^ (k : ℕ))⁻¹ := by
  rw [C8eigen, zeta8_pow_eq, exp_add_inv]

/-- The basic cyclic identity: for an 8-th root of unity `w`,
`w^(i+1) + w^(i-1) = w^i * (w + w⁻¹)`, with exponents taken cyclically. -/
lemma pow_cycle_ident (w : ℂ) (hw : w ^ 8 = 1) (i : Fin 8) :
    w ^ ((i + 1 : Fin 8) : ℕ) + w ^ ((i - 1 : Fin 8) : ℕ) = w ^ (i : ℕ) * (w + w⁻¹) := by
  have hinv : w⁻¹ = w ^ 7 := inv_eq_of_mul_eq_one_right (by linear_combination hw)
  rw [hinv]
  fin_cases i <;> norm_num [Fin.val_add, Fin.val_sub]
  · linear_combination -hw
  · linear_combination -w * hw
  · linear_combination -w ^ 2 * hw
  · linear_combination -w ^ 3 * hw
  · linear_combination -w ^ 4 * hw
  · linear_combination -w ^ 5 * hw
  · linear_combination -(1 + w ^ 6) * hw

/-- Multiplying by the adjacency matrix of `C₈` picks out the two cyclic neighbours. -/
lemma C8adj_sum (i : Fin 8) (f : Fin 8 → ℂ) :
    ∑ l, C8adj i l * f l = f (i + 1) + f (i - 1) := by
  simp only [C8adj]
  fin_cases i <;>
    simp +decide [Fin.sum_univ_eight, show (-1 : Fin 8) = 7 from by decide] <;> ring

/-- The columns of the DFT matrix are eigenvectors of the adjacency matrix, with
eigenvalues `2 cos (2πk/8)`. -/
lemma C8adj_mul_dft : C8adj * C8dft = C8dft * Matrix.diagonal C8eigen := by
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  rw [C8adj_sum i (fun l => C8dft l j)]
  simp only [C8dft, Matrix.vandermonde_apply, C8eigen_eq]
  have key : ∀ m : ℕ, (zeta8 ^ m) ^ (j : ℕ) = (zeta8 ^ (j : ℕ)) ^ m := by
    intro m
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [key, key, key]
  exact pow_cycle_ident _ (by rw [← pow_mul, Nat.mul_comm, pow_mul, zeta8_pow_eight, one_pow]) i

lemma C8dft_isUnit : IsUnit C8dft := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, C8dft]
  refine Matrix.det_vandermonde_ne_zero_iff.mpr ?_
  intro a b h
  exact Fin.ext (zeta8_prim.pow_inj a.isLt b.isLt h)

/-- `C8adj` is indeed the adjacency matrix of Mathlib's cycle graph on `8` vertices. -/
lemma C8adj_eq_adjMatrix : C8adj = (SimpleGraph.cycleGraph 8).adjMatrix ℂ := by
  ext i j
  simp only [C8adj, SimpleGraph.adjMatrix_apply, SimpleGraph.cycleGraph_adj]
  congr 1
  revert i j
  decide

lemma C8adj_charpoly :
    C8adj.charpoly = ∏ k : Fin 8, (X - C (2 * Real.cos (2 * Real.pi * k / 8) : ℂ)) := by
  obtain ⟨u, hu⟩ := C8dft_isUnit
  have hconj :
      C8adj = u.val * Matrix.diagonal C8eigen * (u⁻¹ : (Matrix (Fin 8) (Fin 8) ℂ)ˣ).val := by
    rw [Units.eq_mul_inv_iff_mul_eq, hu]
    exact C8adj_mul_dft
  rw [hconj, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]
  rfl

/-- **Hückel theory for cyclic C₈.** The characteristic polynomial of the adjacency
matrix of the cycle graph `C₈` factors completely with roots `2 cos (2πk/8)`,
`k = 0, …, 7`; that is, the adjacency eigenvalues of `C₈` are exactly
`2 cos (2πk/8)` for `k = 0, …, 7` (counted with multiplicity). -/
theorem huckel_C8 :
    ((SimpleGraph.cycleGraph 8).adjMatrix ℂ).charpoly
      = ∏ k : Fin 8, (X - C (2 * Real.cos (2 * Real.pi * k / 8) : ℂ)) := by
  rw [← C8adj_eq_adjMatrix, C8adj_charpoly]

/-- The multiset of eigenvalues (roots of the characteristic polynomial, with
multiplicity) of the adjacency matrix of `C₈` is `{2 cos (2πk/8) : k = 0, …, 7}`. -/
theorem huckel_C8_eigenvalues :
    ((SimpleGraph.cycleGraph 8).adjMatrix ℂ).charpoly.roots
      = (Finset.univ : Finset (Fin 8)).val.map
          (fun k => (2 * Real.cos (2 * Real.pi * k / 8) : ℂ)) := by
  rw [huckel_C8, Polynomial.roots_prod_X_sub_C]

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

