/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not allow a module docstring before the import commands, so the required
header appears here as an ordinary block comment; the text is otherwise verbatim.)
-/

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

namespace Chem

open Complex Polynomial Matrix SimpleGraph

/-- The adjacency matrix (over `ℂ`) of the cycle graph `C₁₆`, i.e. the Hückel matrix of
cyclic C₁₆ in units where the Coulomb integral is `0` and the resonance integral is `1`. -/
noncomputable def C16Adj : Matrix (Fin 16) (Fin 16) ℂ :=
  (SimpleGraph.cycleGraph 16).adjMatrix ℂ

/-- The Hückel eigenvalues of `C₁₆`: `2 cos (2πk/16)`, `k = 0, …, 15`. -/
noncomputable def huckelEigval (k : Fin 16) : ℝ := 2 * Real.cos (2 * Real.pi * k / 16)

/-- A primitive 16th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 16)

/-- The character `Fin 16 → ℂ` given by `a ↦ ω ^ a`. -/
noncomputable def echar (a : Fin 16) : ℂ := om ^ (a : ℕ)

/-- The (unnormalized) discrete Fourier matrix. -/
noncomputable def Umat : Matrix (Fin 16) (Fin 16) ℂ := Matrix.of fun i j => echar (i * j)

/-- The inverse of the discrete Fourier matrix. -/
noncomputable def Vmat : Matrix (Fin 16) (Fin 16) ℂ :=
  Matrix.of fun i j => (16 : ℂ)⁻¹ * (echar (i * j))⁻¹

/-- The diagonal matrix of Hückel eigenvalues. -/
noncomputable def Dmat : Matrix (Fin 16) (Fin 16) ℂ :=
  Matrix.diagonal fun k => (huckelEigval k : ℂ)

theorem om_isPrimitiveRoot : IsPrimitiveRoot om 16 := by
  simpa [om] using Complex.isPrimitiveRoot_exp 16 (by norm_num)

theorem om_pow_sixteen : om ^ (16 : ℕ) = 1 := om_isPrimitiveRoot.pow_eq_one

theorem om_pow_mod (n : ℕ) : om ^ (n % 16) = om ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 16]
  rw [pow_add, pow_mul, om_pow_sixteen, one_pow, one_mul]

theorem echar_add (a b : Fin 16) : echar (a + b) = echar a * echar b := by
  simp only [echar, Fin.val_add, ← pow_add]
  rw [om_pow_mod]

theorem echar_zero : echar 0 = 1 := by simp [echar]

theorem echar_ne_zero (a : Fin 16) : echar a ≠ 0 := by
  simp [echar, om, Complex.exp_ne_zero]

theorem echar_neg (a : Fin 16) : echar (-a) = (echar a)⁻¹ := by
  have h : echar (-a) * echar a = 1 := by rw [← echar_add, neg_add_cancel, echar_zero]
  exact eq_inv_of_mul_eq_one_left h

theorem echar_eq_one_iff (a : Fin 16) : echar a = 1 ↔ a = 0 := by
  rw [echar, om_isPrimitiveRoot.pow_eq_one_iff_dvd]
  refine ⟨fun h => Fin.ext (by simpa using Nat.eq_zero_of_dvd_of_lt h a.isLt), ?_⟩
  rintro rfl
  exact ⟨0, rfl⟩

theorem echar_mul_pow (a b : Fin 16) : echar (a * b) = (echar b) ^ (a : ℕ) := by
  simp only [echar, Fin.val_mul, ← pow_mul]
  rw [om_pow_mod, mul_comm]

theorem echar_pow_sixteen (b : Fin 16) : (echar b) ^ (16 : ℕ) = 1 := by
  rw [echar, ← pow_mul, mul_comm, pow_mul, om_pow_sixteen, one_pow]

theorem echar_sum (b : Fin 16) :
    (∑ k : Fin 16, echar (k * b)) = if b = 0 then (16 : ℂ) else 0 := by
  simp only [echar_mul_pow]
  by_cases hb : b = 0
  · subst hb
    simp [echar]
  · rw [if_neg hb]
    have hw : echar b ≠ 1 := fun h => hb ((echar_eq_one_iff b).1 h)
    rw [Fin.sum_univ_eq_sum_range (fun k => (echar b) ^ k) 16, geom_sum_eq hw,
      echar_pow_sixteen]
    simp

theorem echar_eq_exp (j : Fin 16) :
    echar j = Complex.exp (((2 * Real.pi * (j : ℕ) / 16 : ℝ) : ℂ) * Complex.I) := by
  rw [echar, om, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem echar_add_inv (j : Fin 16) : echar j + (echar j)⁻¹ = (huckelEigval j : ℂ) := by
  rw [echar_eq_exp, ← Complex.exp_neg, neg_mul_eq_neg_mul, Complex.exp_mul_I, Complex.exp_mul_I]
  simp [huckelEigval, Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos]
  ring

theorem Umat_mul_Vmat : Umat * Vmat = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have key : ∀ k : Fin 16, Umat i k * Vmat k j = (16 : ℂ)⁻¹ * echar (k * (i - j)) := by
    intro k
    have h1 : echar (i * k) = echar (k * (i - j)) * echar (k * j) := by
      rw [← echar_add]
      congr 1
      rw [← mul_add, sub_add_cancel, mul_comm]
    simp only [Umat, Vmat, Matrix.of_apply, h1]
    rw [mul_comm ((16 : ℂ)⁻¹), ← mul_assoc, mul_assoc _ (echar (k * j)),
      mul_inv_cancel₀ (echar_ne_zero _), mul_one, mul_comm]
  simp only [key, ← Finset.mul_sum, echar_sum, Matrix.one_apply, sub_eq_zero]
  split <;> norm_num

theorem Vmat_mul_Umat : Vmat * Umat = 1 := mul_eq_one_comm.mp Umat_mul_Vmat

theorem c16_adj_iff (i k : Fin 16) :
    (SimpleGraph.cycleGraph 16).Adj i k ↔ (k = i - 1 ∨ k = i + 1) := by
  revert i k
  decide

theorem C16Adj_mul_Umat : C16Adj * Umat = Umat * Dmat := by
  ext i j
  have hne : i - 1 ≠ i + 1 := by revert i; decide
  have key : ∀ k : Fin 16, C16Adj i k * Umat k j
      = (if k = i - 1 then Umat k j else 0) + (if k = i + 1 then Umat k j else 0) := by
    intro k
    rw [C16Adj, SimpleGraph.adjMatrix_apply, if_congr (c16_adj_iff i k) rfl rfl]
    by_cases h1 : k = i - 1 <;> by_cases h2 : k = i + 1 <;> simp_all
  rw [Matrix.mul_apply]
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ, Finset.mem_univ,
    if_pos]
  have e1 : Umat (i - 1) j = echar (i * j) * (echar j)⁻¹ := by
    simp only [Umat, Matrix.of_apply]
    rw [show (i - 1) * j = i * j + (-j) by rw [sub_mul, one_mul, sub_eq_add_neg], echar_add,
      echar_neg]
  have e2 : Umat (i + 1) j = echar (i * j) * echar j := by
    simp only [Umat, Matrix.of_apply]
    rw [show (i + 1) * j = i * j + j by rw [add_mul, one_mul], echar_add]
  rw [e1, e2, Dmat, Matrix.mul_diagonal, ← mul_add, add_comm ((echar j)⁻¹), echar_add_inv]
  simp [Umat]

theorem C16Adj_eq_conj : C16Adj = Umat * Dmat * Vmat := by
  calc C16Adj = C16Adj * (Umat * Vmat) := by rw [Umat_mul_Vmat, Matrix.mul_one]
    _ = (C16Adj * Umat) * Vmat := by rw [Matrix.mul_assoc]
    _ = Umat * Dmat * Vmat := by rw [C16Adj_mul_Umat]

theorem C16Adj_charpoly :
    C16Adj.charpoly = ∏ k : Fin 16, (X - C ((huckelEigval k : ℂ))) := by
  let M : (Matrix (Fin 16) (Fin 16) ℂ)ˣ := ⟨Umat, Vmat, Umat_mul_Vmat, Vmat_mul_Umat⟩
  have hconj : ((M : Matrix (Fin 16) (Fin 16) ℂ) * Dmat * (↑M⁻¹ : Matrix (Fin 16) (Fin 16) ℂ)
      ).charpoly = Dmat.charpoly := Matrix.charpoly_units_conj M Dmat
  have hM : (M : Matrix (Fin 16) (Fin 16) ℂ) = Umat := rfl
  have hMinv : (↑M⁻¹ : Matrix (Fin 16) (Fin 16) ℂ) = Vmat := rfl
  rw [hM, hMinv] at hconj
  rw [C16Adj_eq_conj, hconj, Dmat, Matrix.charpoly_diagonal]

/-- **Hückel theory for cyclic C₁₆.**  The adjacency (Hückel) matrix of the cycle graph `C₁₆`
has characteristic polynomial `∏_{k=0}^{15} (X - 2 cos (2πk/16))`, and hence its spectrum,
i.e. its set of eigenvalues, is exactly `{2 cos (2πk/16) : k = 0, …, 15}`. -/
theorem huckel_C16 :
    C16Adj.charpoly = ∏ k : Fin 16, (X - C ((huckelEigval k : ℂ))) ∧
      spectrum ℂ C16Adj = {z : ℂ | ∃ k : Fin 16, z = (huckelEigval k : ℂ)} := by
  refine ⟨C16Adj_charpoly, ?_⟩
  ext z
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, C16Adj_charpoly, Polynomial.IsRoot.def,
    Polynomial.eval_prod]
  simp [Finset.prod_eq_zero_iff, sub_eq_zero]

end Chem

