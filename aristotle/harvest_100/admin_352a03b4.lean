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

/-
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators Real
open Polynomial Matrix

namespace Chem

/-- A primitive 12-th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 12)

/-- Adjacency matrix of the cycle graph `C₁₂` (indices in `Fin 12`, with cyclic arithmetic:
`i` is adjacent exactly to `i + 1` and `i - 1`). -/
def adjC12 : Matrix (Fin 12) (Fin 12) ℂ :=
  fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

/-- The Hückel eigenvalues `2 cos (2πk/12)` of `C₁₂`. -/
noncomputable def eigC12 (k : Fin 12) : ℂ := 2 * Real.cos (2 * Real.pi * k / 12)

/-- The discrete Fourier transform matrix, which diagonalizes `adjC12`. -/
noncomputable def dftC12 : Matrix (Fin 12) (Fin 12) ℂ :=
  fun i k => om ^ (i.val * k.val)

/-- The adjacency matrix is symmetric, as it must be for an undirected graph. -/
lemma adjC12_transpose : adjC12ᵀ = adjC12 := by
  ext i j
  have h : (i = j + 1 ∨ i = j - 1) ↔ (j = i + 1 ∨ j = i - 1) := by revert i j; decide
  simp only [Matrix.transpose_apply, adjC12, h]

/-- The cycle graph has no self-loops. -/
lemma adjC12_diag (i : Fin 12) : adjC12 i i = 0 := by
  have h : ¬ (i = i + 1 ∨ i = i - 1) := by revert i; decide
  simp only [adjC12, if_neg h]

lemma isPrimitiveRoot_om : IsPrimitiveRoot om 12 := by
  have := Complex.isPrimitiveRoot_exp 12 (by norm_num)
  simpa [om] using this

lemma om_pow_twelve : om ^ 12 = 1 := isPrimitiveRoot_om.pow_eq_one

lemma om_pow_congr {a b : ℕ} (h : a ≡ b [MOD 12]) : om ^ a = om ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 12]
  conv_rhs => rw [← Nat.div_add_mod b 12]
  simp only [pow_add, pow_mul, om_pow_twelve, one_pow, one_mul]
  exact congrArg _ h

lemma om_pow_eq_exp (m : ℕ) :
    om ^ m = Complex.exp (((2 * Real.pi * m / 12 : ℝ) : ℂ) * Complex.I) := by
  rw [om, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `ω^k + ω^(-k) = 2 cos (2πk/12)`, written using `ω^(12-k)` for `ω^(-k)`. -/
lemma om_add_inv (k : Fin 12) : om ^ k.val + om ^ (12 - k.val) = eigC12 k := by
  have hk : k.val ≤ 12 := k.isLt.le
  rw [om_pow_eq_exp, om_pow_eq_exp, Complex.exp_mul_I, Complex.exp_mul_I, eigC12]
  have h1 : ((12 - k.val : ℕ) : ℝ) = 12 - (k.val : ℝ) := by
    push_cast [Nat.cast_sub hk]; ring
  rw [h1]
  have h2 : (2 * Real.pi * (12 - (k.val : ℝ)) / 12)
      = 2 * Real.pi - (2 * Real.pi * k.val / 12) := by ring
  rw [h2]
  push_cast
  rw [Complex.cos_sub, Complex.sin_sub]
  simp [Complex.cos_two_pi, Complex.sin_two_pi]
  ring

lemma sum_two_ite (a b : Fin 12) (hab : a ≠ b) (f : Fin 12 → ℂ) :
    ∑ j, (if j = a ∨ j = b then (1 : ℂ) else 0) * f j = f a + f b := by
  have key : ∀ j : Fin 12, (if j = a ∨ j = b then (1 : ℂ) else 0) * f j
      = (if j = a then f j else 0) + (if j = b then f j else 0) := by
    intro j
    by_cases h1 : j = a <;> by_cases h2 : j = b <;> simp_all
  rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ a f, Finset.sum_ite_eq' Finset.univ b f]
  simp

/-- The columns of the DFT matrix are eigenvectors of the adjacency matrix. -/
lemma adj_mul_dft : adjC12 * dftC12 = dftC12 * Matrix.diagonal eigC12 := by
  ext i k
  have hne : i + 1 ≠ i - 1 := by revert i; decide
  have hsucc : (i + 1).val = (i.val + 1) % 12 := by simp [Fin.val_add]
  have hpred : (i - 1).val = (i.val + 11) % 12 := by revert i; decide
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  rw [show (∑ j, adjC12 i j * dftC12 j k)
      = ∑ j, (if j = i + 1 ∨ j = i - 1 then (1 : ℂ) else 0) * dftC12 j k from rfl,
    sum_two_ite _ _ hne]
  have e1 : dftC12 (i + 1) k = om ^ (i.val * k.val + k.val) := by
    rw [dftC12, hsucc]
    refine om_pow_congr ?_
    have h1 : ((i.val + 1) % 12) * k.val ≡ (i.val + 1) * k.val [MOD 12] :=
      (Nat.mod_modEq (i.val + 1) 12).mul_right k.val
    have h2 : (i.val + 1) * k.val = i.val * k.val + k.val := by ring
    rw [h2] at h1
    exact h1
  have e2 : dftC12 (i - 1) k = om ^ (i.val * k.val + (12 - k.val)) := by
    rw [dftC12, hpred]
    refine om_pow_congr ?_
    have h1 : ((i.val + 11) % 12) * k.val ≡ (i.val + 11) * k.val [MOD 12] :=
      (Nat.mod_modEq (i.val + 11) 12).mul_right k.val
    have h2 : (i.val + 11) * k.val = i.val * k.val + 11 * k.val := by ring
    have h3 : i.val * k.val + 11 * k.val ≡ i.val * k.val + (12 - k.val) [MOD 12] := by
      unfold Nat.ModEq; omega
    exact h1.trans (h2 ▸ h3)
  rw [e1, e2, dftC12, ← om_add_inv k, pow_add, pow_add]
  ring

lemma dft_eq_vandermonde : dftC12 = Matrix.vandermonde (fun i : Fin 12 => om ^ i.val) := by
  ext i k
  simp [dftC12, Matrix.vandermonde, ← pow_mul]

lemma dft_det_ne_zero : dftC12.det ≠ 0 := by
  rw [dft_eq_vandermonde, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr (fun i _ => Finset.prod_ne_zero_iff.mpr (fun j hj => ?_))
  have hij : i < j := Finset.mem_Ioi.mp hj
  refine sub_ne_zero.mpr (fun h => ?_)
  have := isPrimitiveRoot_om.pow_inj j.isLt i.isLt h
  omega

/-- **Hückel theory for `C₁₂`**: the characteristic polynomial of the adjacency matrix of the
cycle graph `C₁₂` factors as `∏ₖ (X - 2 cos (2πk/12))`, i.e. the adjacency eigenvalues of `C₁₂`
are exactly `2 cos (2πk/12)` for `k = 0, …, 11`, counted with multiplicity. -/
theorem huckel_C12 :
    adjC12.charpoly = ∏ k : Fin 12, (X - C (2 * Real.cos (2 * Real.pi * k / 12) : ℂ)) := by
  obtain ⟨M, hM⟩ := (Matrix.isUnit_iff_isUnit_det dftC12).mpr
    (isUnit_iff_ne_zero.mpr dft_det_ne_zero)
  set N : Matrix (Fin 12) (Fin 12) ℂ := (M : Matrix (Fin 12) (Fin 12) ℂ) with hN
  set Ninv : Matrix (Fin 12) (Fin 12) ℂ := ((M⁻¹ : (Matrix (Fin 12) (Fin 12) ℂ)ˣ) :
    Matrix (Fin 12) (Fin 12) ℂ) with hNinv
  have h1 : N * Ninv = 1 := by rw [hN, hNinv, ← Units.val_mul]; simp
  have hconj : adjC12 = N * Matrix.diagonal eigC12 * Ninv := by
    calc adjC12 = adjC12 * (N * Ninv) := by rw [h1, mul_one]
    _ = (adjC12 * dftC12) * Ninv := by rw [hM, mul_assoc]
    _ = N * Matrix.diagonal eigC12 * Ninv := by rw [adj_mul_dft, hM]
  rw [hconj, hN, hNinv, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]
  rfl

/-- The explicit eigenvectors: the `k`-th DFT column `j ↦ ω^(jk)` is an eigenvector of the
adjacency matrix of `C₁₂` with eigenvalue `2 cos (2πk/12)`. -/
theorem huckel_C12_eigenvector (k : Fin 12) :
    adjC12.mulVec (fun j : Fin 12 => om ^ (j.val * k.val))
      = (2 * Real.cos (2 * Real.pi * k / 12) : ℂ) • (fun j : Fin 12 => om ^ (j.val * k.val)) := by
  funext i
  have hi := congrFun (congrFun adj_mul_dft i) k
  rw [Matrix.mul_apply, Matrix.mul_diagonal] at hi
  simpa [Matrix.mulVec, dotProduct, dftC12, eigC12, mul_comm] using hi

end Chem

