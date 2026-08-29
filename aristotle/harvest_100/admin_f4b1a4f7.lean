/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The adjacency (Hückel) matrix of the cycle graph `C₁₄` is diagonalised by the discrete Fourier
transform on `ZMod 14`; its characteristic polynomial is therefore
`∏_{k=0}^{13} (X - 2 cos (2πk/14))`, i.e. its eigenvalues are `2 cos (2πk/14)` for `k = 0, …, 13`.
-/

open Complex Polynomial Matrix

namespace Chem

noncomputable section

/-- A primitive 14-th root of unity. -/
noncomputable def zeta14 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 14)

theorem isPrimitiveRoot_zeta14 : IsPrimitiveRoot zeta14 14 := by
  simpa [zeta14] using Complex.isPrimitiveRoot_exp 14 (by norm_num)

theorem zeta14_pow : zeta14 ^ (14 : ℕ) = 1 := isPrimitiveRoot_zeta14.pow_eq_one

/-- The standard additive character of `ZMod 14`, `a ↦ ζ ^ a`. -/
noncomputable def chi : AddChar (ZMod 14) ℂ := AddChar.zmodChar 14 zeta14_pow

theorem chi_apply (a : ZMod 14) : chi a = zeta14 ^ a.val := rfl

theorem chi_isPrimitive : chi.IsPrimitive :=
  AddChar.zmodChar_primitive_of_primitive_root 14 isPrimitiveRoot_zeta14

/-- The Hückel (adjacency) matrix of the cycle `C₁₄`, with vertices indexed by `ZMod 14`:
`i` and `j` are adjacent iff they differ by `1` modulo `14`. -/
def adjC14 : Matrix (ZMod 14) (ZMod 14) ℂ :=
  fun i j => if i - j = 1 ∨ j - i = 1 then 1 else 0

/-- `adjC14` is exactly the adjacency matrix of Mathlib's cycle graph on 14 vertices
(`ZMod 14` and `Fin 14` are the same index type). -/
theorem adjC14_eq_adjMatrix_cycleGraph :
    adjC14 = (SimpleGraph.cycleGraph 14).adjMatrix ℂ := by
  ext i j
  rw [SimpleGraph.adjMatrix_apply]
  simp only [adjC14]
  congr 1
  simp [SimpleGraph.cycleGraph_adj]

/-- The angle `2πk/14`. -/
noncomputable def theta (k : ℕ) : ℝ := 2 * Real.pi * k / 14

/-- The (unnormalised) discrete Fourier transform matrix on `ZMod 14`. -/
noncomputable def dftU : Matrix (ZMod 14) (ZMod 14) ℂ := fun i k => chi (i * k)

/-- The inverse of `dftU`. -/
noncomputable def dftV : Matrix (ZMod 14) (ZMod 14) ℂ :=
  fun k j => (14 : ℂ)⁻¹ * chi (-(k * j))

/-- The diagonal matrix of Hückel eigenvalues `2 cos (2πk/14)`. -/
noncomputable def eigD : Matrix (ZMod 14) (ZMod 14) ℂ :=
  Matrix.diagonal fun k => ((2 * Real.cos (theta k.val) : ℝ) : ℂ)

theorem chi_eq_exp (a : ZMod 14) : chi a = Complex.exp (theta a.val * Complex.I) := by
  show zeta14 ^ a.val = _
  rw [zeta14, ← Complex.exp_nat_mul]
  congr 1
  unfold theta
  push_cast
  ring

/-- `ζ^k + ζ^{-k} = 2 cos (2πk/14)`. -/
theorem chi_add_chi_neg (k : ZMod 14) :
    chi k + chi (-k) = ((2 * Real.cos (theta k.val) : ℝ) : ℂ) := by
  have h1 : chi k * chi (-k) = 1 := by
    rw [← AddChar.map_add_eq_mul]; simp
  have hk := chi_eq_exp k
  rw [hk] at h1
  have h2 : chi (-k) = Complex.exp (-((theta k.val : ℂ) * I)) := by
    rw [Complex.exp_neg]
    exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h1)
  rw [hk, h2]
  push_cast [Complex.ofReal_cos]
  rw [Complex.two_cos]
  ring_nf

/-- The columns of the DFT matrix are eigenvectors of the adjacency matrix. -/
theorem adj_mul_dftU : adjC14 * dftU = dftU * eigD := by
  ext i k
  have hne : (i - 1 : ZMod 14) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 14) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  have hR : (dftU * eigD) i k = dftU i k * ((2 * Real.cos (theta k.val) : ℝ) : ℂ) :=
    Matrix.mul_diagonal _ _ _ _
  rw [Matrix.mul_apply, hR]
  have key : ∀ j : ZMod 14, adjC14 i j * dftU j k
      = (if j = i - 1 then chi (j * k) else 0) + (if j = i + 1 then chi (j * k) else 0) := by
    intro j
    by_cases h1 : j = i - 1
    · subst h1
      simp [adjC14, dftU, sub_sub_cancel, hne]
    · by_cases h2 : j = i + 1
      · subst h2
        simp [adjC14, dftU, h1, add_sub_cancel_left]
      · have h3 : ¬ (i - j = 1 ∨ j - i = 1) := by
          rintro (h | h)
          · exact h1 (by linear_combination -h)
          · exact h2 (by linear_combination h)
        simp [adjC14, dftU, h1, h2, h3]
  rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (i - 1) (fun j => chi (j * k)),
    Finset.sum_ite_eq' Finset.univ (i + 1) (fun j => chi (j * k))]
  simp only [Finset.mem_univ, if_true]
  have e1 : ((i - 1) * k : ZMod 14) = i * k + (-k) := by ring
  have e2 : ((i + 1) * k : ZMod 14) = i * k + k := by ring
  rw [e1, e2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  show chi (i * k) * chi (-k) + chi (i * k) * chi k = chi (i * k) * _
  rw [← mul_add, add_comm (chi (-k)) (chi k), chi_add_chi_neg]

/-- Orthogonality of characters on `ZMod 14`. -/
theorem chi_sum (a : ZMod 14) : ∑ k : ZMod 14, chi (a * k) = if a = 0 then 14 else 0 := by
  by_cases ha : a = 0
  · subst ha; simp [ZMod.card]
  · rw [if_neg ha]
    simpa [AddChar.mulShift_apply] using AddChar.sum_eq_zero_of_ne_one (chi_isPrimitive ha)

theorem dftU_mul_dftV : dftU * dftV = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have h : ∀ k : ZMod 14, dftU i k * dftV k j = (14 : ℂ)⁻¹ * chi ((i - j) * k) := by
    intro k
    show chi (i * k) * ((14 : ℂ)⁻¹ * chi (-(k * j))) = _
    rw [show ((i - j) * k : ZMod 14) = i * k + (-(k * j)) by ring, AddChar.map_add_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun k _ => h k), ← Finset.mul_sum, chi_sum]
  by_cases hij : i = j
  · subst hij; norm_num
  · have : i - j ≠ 0 := sub_ne_zero_of_ne hij
    simp [this, hij]

theorem dftV_mul_dftU : dftV * dftU = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have h : ∀ k : ZMod 14, dftV i k * dftU k j = (14 : ℂ)⁻¹ * chi ((j - i) * k) := by
    intro k
    show ((14 : ℂ)⁻¹ * chi (-(i * k))) * chi (k * j) = _
    rw [show ((j - i) * k : ZMod 14) = -(i * k) + k * j by ring, AddChar.map_add_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun k _ => h k), ← Finset.mul_sum, chi_sum]
  by_cases hij : i = j
  · subst hij; norm_num
  · have : j - i ≠ 0 := sub_ne_zero_of_ne (Ne.symm hij)
    simp [this, hij]

/-- `dftU` as a unit of the matrix ring. -/
noncomputable def dftUnit : (Matrix (ZMod 14) (ZMod 14) ℂ)ˣ :=
  ⟨dftU, dftV, dftU_mul_dftV, dftV_mul_dftU⟩

/-- The adjacency matrix of `C₁₄` is conjugate to the diagonal matrix of the numbers
`2 cos (2πk/14)`. -/
theorem adj_conj : adjC14 = dftUnit.val * eigD * dftUnit⁻¹.val := by
  have h : adjC14 * dftU * dftV = dftU * eigD * dftV := by rw [adj_mul_dftU]
  rw [mul_assoc, dftU_mul_dftV, mul_one] at h
  exact h

theorem charpoly_adj_prod_zmod :
    adjC14.charpoly = ∏ k : ZMod 14, (X - C ((2 * Real.cos (theta k.val) : ℝ) : ℂ)) := by
  rw [adj_conj, Matrix.charpoly_units_conj]
  exact Matrix.charpoly_diagonal _

/-- **Hückel theory for the cycle `C₁₄`.**  The characteristic polynomial of the adjacency
matrix of the cycle graph `C₁₄` factors as `∏_{k=0}^{13} (X - 2 cos (2πk/14))`; i.e. the
adjacency eigenvalues of `C₁₄` are exactly the numbers `2 cos (2πk/14)`, `k = 0, …, 13`
(listed with multiplicity). -/
theorem huckel_C14 :
    adjC14.charpoly =
      ∏ k ∈ Finset.range 14, (X - C ((2 * Real.cos (2 * Real.pi * k / 14) : ℝ) : ℂ)) := by
  rw [charpoly_adj_prod_zmod]
  symm
  refine Finset.prod_nbij' (fun k => (k : ZMod 14)) (fun k => ZMod.val k) ?_ ?_ ?_ ?_ ?_ <;>
    intro a ha <;> simp_all [theta, ZMod.natCast_val, ZMod.val_lt, Nat.mod_eq_of_lt]

/-- The eigenvalues of the adjacency matrix of `C₁₄` are precisely the numbers
`2 cos (2πk/14)` for `k = 0, …, 13`. -/
theorem huckel_C14_spectrum (mu : ℂ) :
    adjC14.charpoly.IsRoot mu ↔
      ∃ k : ℕ, k < 14 ∧ mu = ((2 * Real.cos (2 * Real.pi * k / 14) : ℝ) : ℂ) := by
  rw [Polynomial.IsRoot, huckel_C14, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, hk, h⟩
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at h
    exact ⟨k, Finset.mem_range.mp hk, h⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, Finset.mem_range.mpr hk, by simp⟩

/-- The same statement for Mathlib's cycle graph `C₁₄`: the characteristic polynomial of its
adjacency matrix is `∏_{k=0}^{13} (X - 2 cos (2πk/14))`. -/
theorem huckel_C14_cycleGraph :
    ((SimpleGraph.cycleGraph 14).adjMatrix ℂ).charpoly =
      ∏ k ∈ Finset.range 14, (X - C ((2 * Real.cos (2 * Real.pi * k / 14) : ℝ) : ℂ)) := by
  rw [← adjC14_eq_adjMatrix_cycleGraph]
  exact huckel_C14

end

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

