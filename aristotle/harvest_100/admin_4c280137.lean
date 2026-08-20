import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Polynomial Finset

namespace Chem

/-- A primitive 11th root of unity. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / (11 : ℕ))

lemma zeta_primitive : IsPrimitiveRoot zeta 11 := Complex.isPrimitiveRoot_exp 11 (by norm_num)

lemma zeta_pow_eleven : zeta ^ 11 = 1 := zeta_primitive.pow_eq_one

/-- The character `m ↦ ζ^m` of `Fin 11 = ZMod 11`. -/
noncomputable def ee (m : Fin 11) : ℂ := zeta ^ m.val

/-- The Hückel eigenvalues of the cycle `C₁₁` (in units of `β`, with `α = 0`). -/
noncomputable def huckelEigenvalue (k : Fin 11) : ℂ :=
  2 * ((Real.cos (2 * Real.pi * (k : ℕ) / 11) : ℝ) : ℂ)

/-- The discrete Fourier transform matrix, whose columns are the eigenvectors. -/
noncomputable def dftMatrix : Matrix (Fin 11) (Fin 11) ℂ := fun j k => ee (j * k)

/-- The (scaled) inverse discrete Fourier transform matrix. -/
noncomputable def dftMatrixInv : Matrix (Fin 11) (Fin 11) ℂ :=
  fun j k => (11 : ℂ)⁻¹ * ee (-(j * k))

lemma zeta_pow_mod (n : ℕ) : zeta ^ (n % 11) = zeta ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 11]
  rw [pow_add, pow_mul, zeta_pow_eleven, one_pow, one_mul]

lemma ee_add (a b : Fin 11) : ee (a + b) = ee a * ee b := by
  unfold ee
  rw [Fin.val_add, zeta_pow_mod, pow_add]

lemma ee_mul (a b : Fin 11) : ee (a * b) = ee b ^ (a : ℕ) := by
  unfold ee
  rw [Fin.val_mul, zeta_pow_mod, ← pow_mul, mul_comm]

lemma ee_zero : ee 0 = 1 := by simp [ee]

lemma ee_pow_eleven (m : Fin 11) : ee m ^ 11 = 1 := by
  rw [ee, ← pow_mul, mul_comm, pow_mul, zeta_pow_eleven, one_pow]

lemma ee_ne_one {m : Fin 11} (hm : m ≠ 0) : ee m ≠ 1 :=
  zeta_primitive.pow_ne_one_of_pos_of_lt (fun h => hm (Fin.ext h)) m.isLt

lemma ee_exp (k : Fin 11) : ee k = Complex.exp (((2 * Real.pi * (k : ℕ) / 11 : ℝ) : ℂ) * I) := by
  unfold ee zeta
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma ee_add_ee_neg (k : Fin 11) : ee k + ee (-k) = huckelEigenvalue k := by
  have hprod : ee k * ee (-k) = 1 := by rw [← ee_add]; simp [ee_zero]
  have hne : ee k ≠ 0 := by rw [ee_exp]; exact Complex.exp_ne_zero _
  have h2 : ee (-k) = Complex.exp (-(((2 * Real.pi * (k : ℕ) / 11 : ℝ) : ℂ) * I)) := by
    rw [Complex.exp_neg, ← ee_exp]
    field_simp
    linear_combination hprod
  rw [huckelEigenvalue, ee_exp, h2, Complex.ofReal_cos, Complex.cos]
  ring_nf

lemma sum_ee (m : Fin 11) : (∑ l : Fin 11, ee (l * m)) = if m = 0 then 11 else 0 := by
  have h : (∑ l : Fin 11, ee (l * m)) = ∑ i ∈ Finset.range 11, ee m ^ i := by
    rw [← Fin.sum_univ_eq_sum_range fun i => ee m ^ i]
    exact Finset.sum_congr rfl fun l _ => ee_mul l m
  rw [h]
  by_cases hm : m = 0
  · subst hm
    simp [ee_zero]
  · rw [if_neg hm, geom_sum_eq (ee_ne_one hm), ee_pow_eleven, sub_self, zero_div]

/-- Ring identities in `Fin 11 = ZMod 11`. -/
lemma fin11_ring1 (j k l : Fin 11) : j * l + -(l * k) = l * (j - k) := by
  have h : ∀ a b c : ZMod 11, a * c + -(c * b) = c * (a - b) := by
    intro a b c; ring
  exact h j k l

lemma fin11_ring2 (j k : Fin 11) : (j - 1) * k = j * k + -k := by
  have h : ∀ a b : ZMod 11, (a - 1) * b = a * b + -b := by
    intro a b; ring
  exact h j k

lemma fin11_ring3 (j k : Fin 11) : (j + 1) * k = j * k + k := by
  have h : ∀ a b : ZMod 11, (a + 1) * b = a * b + b := by
    intro a b; ring
  exact h j k

lemma dft_mul_inv : dftMatrix * dftMatrixInv = 1 := by
  ext j k
  rw [Matrix.mul_apply]
  have hterm : ∀ l : Fin 11,
      dftMatrix j l * dftMatrixInv l k = (11 : ℂ)⁻¹ * ee (l * (j - k)) := by
    intro l
    simp only [dftMatrix, dftMatrixInv]
    rw [show ee (j * l) * ((11 : ℂ)⁻¹ * ee (-(l * k)))
        = (11 : ℂ)⁻¹ * (ee (j * l) * ee (-(l * k))) by ring, ← ee_add, fin11_ring1]
  rw [Finset.sum_congr rfl fun l _ => hterm l, ← Finset.mul_sum, sum_ee, Matrix.one_apply]
  by_cases hjk : j = k
  · subst hjk; simp
  · rw [if_neg (sub_ne_zero_of_ne hjk), if_neg hjk, mul_zero]

/-- The adjacency matrix of `C₁₁` is diagonalized by the discrete Fourier transform. -/
lemma adj_mul_dft :
    (SimpleGraph.cycleGraph 11).adjMatrix ℂ * dftMatrix
      = dftMatrix * Matrix.diagonal huckelEigenvalue := by
  have hne : ∀ j : Fin 11, j - 1 ≠ j + 1 := by decide
  ext j k
  have hrow : ((SimpleGraph.cycleGraph 11).adjMatrix ℂ * dftMatrix) j k
      = dftMatrix (j - 1) k + dftMatrix (j + 1) k := by
    rw [Matrix.mul_apply]
    have h2 : ∑ l, ((SimpleGraph.cycleGraph 11).adjMatrix ℂ) j l * dftMatrix l k
        = ∑ l ∈ (SimpleGraph.cycleGraph 11).neighborFinset j, dftMatrix l k := by
      rw [← SimpleGraph.adjMatrix_mulVec_apply]
      rfl
    rw [h2, SimpleGraph.cycleGraph_neighborFinset (n := 9) (v := j),
      Finset.sum_pair (hne j)]
  rw [hrow, Matrix.mul_diagonal]
  simp only [dftMatrix]
  rw [fin11_ring2, fin11_ring3, ee_add, ee_add, ← mul_add, add_comm (ee (-k)) (ee k),
    ee_add_ee_neg]

/-- The characteristic polynomial of the adjacency matrix of the cycle graph `C₁₁`
factors as `∏ k, (X - 2cos(2πk/11))`, i.e. the Hückel eigenvalues, with multiplicity,
are `2 cos (2πk/11)` for `k = 0, …, 10`. -/
theorem huckel_C11_charpoly :
    ((SimpleGraph.cycleGraph 11).adjMatrix ℂ).charpoly
      = ∏ k : Fin 11, (X - C ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 11) : ℂ))) := by
  have hQP : dftMatrixInv * dftMatrix = 1 := mul_eq_one_comm.mp dft_mul_inv
  let U : (Matrix (Fin 11) (Fin 11) ℂ)ˣ := ⟨dftMatrix, dftMatrixInv, dft_mul_inv, hQP⟩
  have hA : (SimpleGraph.cycleGraph 11).adjMatrix ℂ
      = U.val * Matrix.diagonal huckelEigenvalue * (U⁻¹).val := by
    show (SimpleGraph.cycleGraph 11).adjMatrix ℂ
      = dftMatrix * Matrix.diagonal huckelEigenvalue * dftMatrixInv
    calc (SimpleGraph.cycleGraph 11).adjMatrix ℂ
        = (SimpleGraph.cycleGraph 11).adjMatrix ℂ * (dftMatrix * dftMatrixInv) := by
          rw [dft_mul_inv, mul_one]
      _ = ((SimpleGraph.cycleGraph 11).adjMatrix ℂ * dftMatrix) * dftMatrixInv := by
          rw [mul_assoc]
      _ = dftMatrix * Matrix.diagonal huckelEigenvalue * dftMatrixInv := by rw [adj_mul_dft]
  rw [hA, Matrix.charpoly_units_conj U, Matrix.charpoly_diagonal]
  rfl

/-- **Hückel theory for `C₁₁`.** The eigenvalues of the adjacency matrix of the cycle graph
`C₁₁` are exactly the numbers `2 cos (2πk/11)` for `k = 0, …, 10`. -/
theorem huckel_C11 :
    spectrum ℂ ((SimpleGraph.cycleGraph 11).adjMatrix ℂ)
      = Set.range fun k : Fin 11 => (2 * Real.cos (2 * Real.pi * (k : ℕ) / 11) : ℂ) := by
  ext mu
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C11_charpoly]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and,
    sub_eq_zero, Set.mem_range]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, hk.symm⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, hk.symm⟩

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

