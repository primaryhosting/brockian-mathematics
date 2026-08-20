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

open Matrix Polynomial

namespace Chem

/-! ## A primitive tenth root of unity and the associated additive character -/

/-- A primitive `10`-th root of unity. -/
noncomputable def zeta10 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 10)

lemma zeta10_isPrimitiveRoot : IsPrimitiveRoot zeta10 10 := by
  have h := Complex.isPrimitiveRoot_exp 10 (by norm_num)
  simpa [zeta10] using h

lemma zeta10_pow_ten : zeta10 ^ (10 : ℕ) = 1 :=
  ((IsPrimitiveRoot.iff_def zeta10 10).mp zeta10_isPrimitiveRoot).left

/-- The additive character `a ↦ ζ ^ a` of `ZMod 10`, where `ζ = exp (2πi/10)`. -/
noncomputable def chi : AddChar (ZMod 10) ℂ := AddChar.zmodChar 10 zeta10_pow_ten

lemma chi_isPrimitive : chi.IsPrimitive :=
  AddChar.zmodChar_primitive_of_primitive_root 10 zeta10_isPrimitiveRoot

lemma chi_apply (a : ZMod 10) : chi a = zeta10 ^ a.val := rfl

lemma chi_eq_exp (a : ZMod 10) :
    chi a = Complex.exp (((2 * Real.pi * a.val / 10 : ℝ) : ℂ) * Complex.I) := by
  rw [chi_apply, zeta10, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-! ## The Hückel eigenvalues, the Fourier matrix and the adjacency matrix of `C₁₀` -/

/-- The `k`-th Hückel eigenvalue of the cycle `C₁₀`, namely `2 cos (2πk/10)`. -/
noncomputable def huckelEigenvalue (k : ZMod 10) : ℂ :=
  ((2 * Real.cos (2 * Real.pi * k.val / 10) : ℝ) : ℂ)

/-- The discrete Fourier matrix `F j k = ζ ^ (jk)`. -/
noncomputable def dftMat : Matrix (ZMod 10) (ZMod 10) ℂ :=
  Matrix.of fun j k => chi (j * k)

/-- The inverse discrete Fourier matrix `F⁻¹ j k = ζ ^ (-jk) / 10`. -/
noncomputable def dftMatInv : Matrix (ZMod 10) (ZMod 10) ℂ :=
  Matrix.of fun j k => (10 : ℂ)⁻¹ * chi (-(j * k))

/-- The adjacency matrix of the cycle graph `C₁₀`, with vertex set identified with `ZMod 10`. -/
noncomputable def C10 : Matrix (ZMod 10) (ZMod 10) ℂ :=
  SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 10)

/-- `ζ ^ k + ζ ^ (-k) = 2 cos (2πk/10)`. -/
lemma chi_add_chi_neg (k : ZMod 10) : chi k + chi (-k) = huckelEigenvalue k := by
  set θ : ℝ := 2 * Real.pi * k.val / 10 with hθ
  have hc : chi k = Complex.exp ((θ : ℂ) * Complex.I) := chi_eq_exp _
  have hne : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have h1 : chi (-k) * Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
    rw [← hc, ← AddChar.map_add_eq_mul]; simp
  have h2 : chi (-k) = Complex.exp (-(θ : ℂ) * Complex.I) := by
    rw [(mul_eq_one_iff_eq_inv₀ hne).mp h1, ← Complex.exp_neg]
    ring_nf
  rw [hc, h2, huckelEigenvalue, ← hθ, Complex.ofReal_mul, Complex.ofReal_cos]
  push_cast
  exact (Complex.two_cos _).symm

/-! ## The Fourier matrix diagonalises the adjacency matrix -/

lemma dftMat_mul_dftMatInv : dftMat * dftMatInv = 1 := by
  ext j k
  rw [Matrix.mul_apply]
  simp only [dftMat, dftMatInv, Matrix.of_apply]
  have hterm : ∀ l : ZMod 10,
      chi (j * l) * ((10 : ℂ)⁻¹ * chi (-(l * k))) = (10 : ℂ)⁻¹ * chi (l * (j - k)) := by
    intro l
    rw [show l * (j - k) = j * l + -(l * k) by ring, AddChar.map_add_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun l _ => hterm l), ← Finset.mul_sum,
    AddChar.sum_mulShift _ chi_isPrimitive]
  by_cases h : j = k
  · subst h
    simp
  · rw [Matrix.one_apply_ne h]
    simp [sub_eq_zero, h]

lemma dftMatInv_mul_dftMat : dftMatInv * dftMat = 1 :=
  mul_eq_one_comm.mp dftMat_mul_dftMatInv

/-- The Fourier matrix as a unit of the matrix ring. -/
noncomputable def dftUnit : (Matrix (ZMod 10) (ZMod 10) ℂ)ˣ :=
  ⟨dftMat, dftMatInv, dftMat_mul_dftMatInv, dftMatInv_mul_dftMat⟩

lemma C10_mul_dftMat : C10 * dftMat = dftMat * Matrix.diagonal huckelEigenvalue := by
  ext j k
  have hnb : (SimpleGraph.cycleGraph 10).neighborFinset j = {j - 1, j + 1} :=
    SimpleGraph.cycleGraph_neighborFinset (n := 8)
  have hne : ∀ j : ZMod 10, j - 1 ≠ j + 1 := by decide
  have hleft : (C10 * dftMat) j k = dftMat (j - 1) k + dftMat (j + 1) k := by
    rw [Matrix.mul_apply]
    have : (∑ l, C10 j l * dftMat l k)
        = (SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 10)).mulVec
            (fun l => dftMat l k) j := rfl
    rw [this, SimpleGraph.adjMatrix_mulVec_apply, hnb]
    exact Finset.sum_pair (hne j)
  rw [hleft, Matrix.mul_diagonal]
  simp only [dftMat, Matrix.of_apply]
  rw [show (j - 1) * k = j * k + -k by ring, show (j + 1) * k = j * k + k by ring,
    AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, ← mul_add, add_comm (chi (-k)) (chi k),
    chi_add_chi_neg]

lemma C10_eq_conj : C10 = (dftUnit : Matrix (ZMod 10) (ZMod 10) ℂ) *
    Matrix.diagonal huckelEigenvalue * (↑dftUnit⁻¹ : Matrix (ZMod 10) (ZMod 10) ℂ) := by
  have h : (↑dftUnit⁻¹ : Matrix (ZMod 10) (ZMod 10) ℂ) = dftMatInv := rfl
  have hU : (dftUnit : Matrix (ZMod 10) (ZMod 10) ℂ) = dftMat := rfl
  rw [h, hU, ← C10_mul_dftMat, mul_assoc, dftMat_mul_dftMatInv, mul_one]

/-! ## Characteristic polynomial and spectrum -/

theorem C10_charpoly :
    C10.charpoly = ∏ k : ZMod 10, (X - C (huckelEigenvalue k)) := by
  rw [C10_eq_conj, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]

theorem C10_spectrum :
    spectrum ℂ C10 = {z : ℂ | ∃ k : ZMod 10, z = huckelEigenvalue k} := by
  ext z
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, C10_charpoly]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero,
    Set.mem_setOf_eq]

/-- **Hückel theory for `C₁₀`.**  The characteristic polynomial of the adjacency matrix of the
cycle graph `C₁₀` is `∏ k, (X - 2 cos (2πk/10))`; consequently its spectrum (the set of
eigenvalues) is exactly `{2 cos (2πk/10) : k = 0, …, 9}`. -/
theorem huckel_C10 :
    (SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 10)).charpoly
        = ∏ k : Fin 10, (X - C ((2 * Real.cos (2 * Real.pi * k.val / 10) : ℝ) : ℂ)) ∧
      spectrum ℂ (SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 10))
        = {z : ℂ | ∃ k : Fin 10, z = ((2 * Real.cos (2 * Real.pi * k.val / 10) : ℝ) : ℂ)} :=
  ⟨C10_charpoly, C10_spectrum⟩

end Chem

