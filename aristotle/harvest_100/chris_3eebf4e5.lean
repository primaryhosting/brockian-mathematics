/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 15

Category: Chemistry.  Target: `Chem.huckel_C15`.

The Hückel (adjacency) eigenvalues of the cycle graph `C₁₅` are `2 cos (2πk/15)`, `k = 0, …, 14`.

The proof diagonalizes the adjacency matrix by the discrete Fourier matrix
`U i k = ζ ^ (k * i)` with `ζ = exp (2πi/15)`, and then uses
`spectrum.units_conjugate` together with `spectrum_diagonal`.
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Chem

open Complex Matrix SimpleGraph Finset

/-- A primitive 15-th root of unity. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 15)

/-- The adjacency matrix of the cycle graph `C₁₅`, over `ℂ`. -/
noncomputable def C15adj : Matrix (Fin 15) (Fin 15) ℂ := (cycleGraph 15).adjMatrix ℂ

/-- The Hückel eigenvalue `2 cos (2πk/15)`. -/
noncomputable def huckelEigenvalue (k : Fin 15) : ℂ :=
  ((2 * Real.cos (2 * Real.pi * k.val / 15) : ℝ) : ℂ)

/-- The eigenvector of `C15adj` associated with `huckelEigenvalue k`. -/
noncomputable def huckelEigenvector (k : Fin 15) : Fin 15 → ℂ := fun i => zeta ^ (k.val * i.val)

/-! ### Basic facts about `zeta` -/

theorem zeta_isPrimitiveRoot : IsPrimitiveRoot zeta 15 := by
  simpa [zeta] using Complex.isPrimitiveRoot_exp 15 (by norm_num)

theorem zeta_pow_fifteen : zeta ^ 15 = 1 := zeta_isPrimitiveRoot.pow_eq_one

theorem zeta_ne_zero : zeta ≠ 0 := by
  simp [zeta, Complex.exp_ne_zero]

theorem orderOf_zeta : orderOf zeta = 15 := zeta_isPrimitiveRoot.eq_orderOf.symm

theorem zeta_isOfFinOrder : IsOfFinOrder zeta :=
  isOfFinOrder_iff_pow_eq_one.2 ⟨15, by norm_num, zeta_pow_fifteen⟩

theorem zeta_pow_eq_iff {a b : ℕ} : zeta ^ a = zeta ^ b ↔ a ≡ b [MOD 15] := by
  rw [zeta_isOfFinOrder.pow_eq_pow_iff_modEq, orderOf_zeta]

theorem zeta_pow_congr {a b : ℕ} (h : a ≡ b [MOD 15]) : zeta ^ a = zeta ^ b :=
  zeta_pow_eq_iff.2 h

theorem zeta_pow_pow_fifteen (m : ℕ) : (zeta ^ m) ^ 15 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, zeta_pow_fifteen, one_pow]

/-! ### The eigenvalues -/

theorem two_cos_eq (t : ℂ) : Complex.exp (t * I) + (Complex.exp (t * I))⁻¹ = 2 * Complex.cos t := by
  rw [← Complex.exp_neg, ← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I]
  simp [Complex.cos_neg, Complex.sin_neg]
  ring

theorem huckelEigenvalue_eq (k : Fin 15) :
    huckelEigenvalue k = zeta ^ (k.val) + (zeta ^ (k.val))⁻¹ := by
  have h1 : zeta ^ (k.val) = Complex.exp ((2 * Real.pi * k.val / 15 : ℝ) * I) := by
    rw [zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [huckelEigenvalue, h1, two_cos_eq]
  push_cast
  ring_nf

/-! ### The eigenvectors -/

theorem C15adj_mulVec (v : Fin 15 → ℂ) (i : Fin 15) :
    C15adj.mulVec v i = v (i + 1) + v (i - 1) := by
  rw [C15adj, SimpleGraph.adjMatrix_mulVec_apply]
  have h : (cycleGraph 15).neighborFinset i = {i + 1, i - 1} := by revert i; decide
  rw [h, Finset.sum_pair (by revert i; decide : i + 1 ≠ i - 1)]

theorem zeta_pow_succ (k i : Fin 15) :
    zeta ^ (k.val * (i + 1).val) = zeta ^ (k.val * i.val) * zeta ^ k.val := by
  rw [← pow_add]
  refine zeta_pow_congr ?_
  have h : (i + 1).val ≡ i.val + 1 [MOD 15] := by revert i; decide
  calc k.val * (i + 1).val ≡ k.val * (i.val + 1) [MOD 15] := Nat.ModEq.mul_left _ h
    _ = k.val * i.val + k.val := by ring

theorem zeta_pow_pred (k i : Fin 15) :
    zeta ^ (k.val * (i - 1).val) = zeta ^ (k.val * i.val) * (zeta ^ k.val)⁻¹ := by
  have h15 : zeta ^ (15 * k.val) = 1 := by rw [pow_mul, zeta_pow_fifteen, one_pow]
  have key : zeta ^ (k.val * (i - 1).val) = zeta ^ (k.val * i.val + 14 * k.val) := by
    refine zeta_pow_congr ?_
    have h : (i - 1).val ≡ i.val + 14 [MOD 15] := by revert i; decide
    calc k.val * (i - 1).val ≡ k.val * (i.val + 14) [MOD 15] := Nat.ModEq.mul_left _ h
      _ = k.val * i.val + 14 * k.val := by ring
  rw [key, pow_add]
  congr 1
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_add]
  have h : 14 * k.val + k.val = 15 * k.val := by ring
  rw [h, h15]

theorem mulVec_huckelEigenvector (k : Fin 15) :
    C15adj.mulVec (huckelEigenvector k) = huckelEigenvalue k • huckelEigenvector k := by
  funext i
  rw [C15adj_mulVec]
  simp only [huckelEigenvector, Pi.smul_apply, smul_eq_mul, huckelEigenvalue_eq]
  rw [zeta_pow_succ, zeta_pow_pred]
  ring

/-! ### Diagonalization by the discrete Fourier matrix -/

/-- The (unnormalized) discrete Fourier matrix: its `k`-th column is `huckelEigenvector k`. -/
noncomputable def dftMatrix : Matrix (Fin 15) (Fin 15) ℂ := fun i k => zeta ^ (k.val * i.val)

/-- The inverse of the discrete Fourier matrix. -/
noncomputable def dftMatrixInv : Matrix (Fin 15) (Fin 15) ℂ :=
  fun k j => (15 : ℂ)⁻¹ * (zeta⁻¹) ^ (k.val * j.val)

theorem dftMatrix_mul_inv : dftMatrix * dftMatrixInv = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  set w : ℂ := zeta ^ i.val * (zeta⁻¹) ^ j.val with hw
  have hterm : ∀ k : Fin 15, dftMatrix i k * dftMatrixInv k j = (15 : ℂ)⁻¹ * w ^ k.val := by
    intro k
    simp only [dftMatrix, dftMatrixInv, hw]
    rw [mul_pow, ← pow_mul, ← pow_mul]
    ring_nf
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum]
  have hwpow : w ^ 15 = 1 := by
    rw [hw, mul_pow, zeta_pow_pow_fifteen, inv_pow, inv_pow, zeta_pow_pow_fifteen, inv_one, mul_one]
  have hsum : ∑ k : Fin 15, w ^ k.val = if i = j then 15 else 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => w ^ k)]
    by_cases hij : i = j
    · subst hij
      have hw1 : w = 1 := by
        rw [hw, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ zeta_ne_zero)]
      simp [hw1]
    · have hwne : w ≠ 1 := by
        rw [hw, inv_pow]
        intro h
        rw [mul_inv_eq_one₀ (pow_ne_zero _ zeta_ne_zero), zeta_pow_eq_iff] at h
        exact hij (Fin.ext (by
          have := i.isLt; have := j.isLt; unfold Nat.ModEq at h; omega))
      rw [geom_sum_eq hwne, hwpow, if_neg hij]
      simp
  rw [hsum]
  by_cases hij : i = j
  · subst hij; rw [if_pos rfl, Matrix.one_apply_eq]; norm_num
  · rw [if_neg hij, Matrix.one_apply_ne hij, mul_zero]

theorem C15adj_mul_dftMatrix :
    C15adj * dftMatrix = dftMatrix * Matrix.diagonal huckelEigenvalue := by
  ext i k
  have hleft : (C15adj * dftMatrix) i k = C15adj.mulVec (huckelEigenvector k) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, dftMatrix, huckelEigenvector]
  rw [hleft, mulVec_huckelEigenvector, Matrix.mul_apply]
  simp [Matrix.diagonal, Pi.smul_apply, dftMatrix, huckelEigenvector, Finset.sum_ite_eq',
    mul_comm]

/-! ### The main theorem -/

/-- The adjacency (Hückel) spectrum of the cycle graph `C₁₅` consists exactly of the numbers
`2 cos (2πk/15)` for `k = 0, …, 14`. -/
theorem huckel_C15 :
    spectrum ℂ ((cycleGraph 15).adjMatrix ℂ) =
      {z : ℂ | ∃ k : Fin 15, z = ((2 * Real.cos (2 * Real.pi * k.val / 15) : ℝ) : ℂ)} := by
  have hinv : Invertible dftMatrix := invertibleOfRightInverse _ _ dftMatrix_mul_inv
  have hA : (cycleGraph 15).adjMatrix ℂ
      = dftMatrix * Matrix.diagonal huckelEigenvalue * (⅟dftMatrix) := by
    rw [← C15adj_mul_dftMatrix, mul_assoc, mul_invOf_self, mul_one, C15adj]
  rw [hA]
  have hu : spectrum ℂ (((unitOfInvertible dftMatrix) : (Matrix (Fin 15) (Fin 15) ℂ)ˣ).val
        * Matrix.diagonal huckelEigenvalue
        * ((unitOfInvertible dftMatrix)⁻¹ : (Matrix (Fin 15) (Fin 15) ℂ)ˣ).val)
      = spectrum ℂ (Matrix.diagonal huckelEigenvalue) := spectrum.units_conjugate
  have hu' : spectrum ℂ (dftMatrix * Matrix.diagonal huckelEigenvalue * (⅟dftMatrix))
      = spectrum ℂ (Matrix.diagonal huckelEigenvalue) := hu
  rw [hu', spectrum_diagonal]
  ext z
  simp [Set.mem_range, huckelEigenvalue, eq_comm]

theorem huckelEigenvector_ne_zero (k : Fin 15) : huckelEigenvector k ≠ 0 := by
  intro h
  have h0 : huckelEigenvector k 0 = 0 := by rw [h]; rfl
  simp [huckelEigenvector] at h0

/-- For each `k`, the vector `i ↦ ζ ^ (k * i)` (with `ζ = exp (2πi/15)`) is a nonzero eigenvector
of the adjacency matrix of `C₁₅` with eigenvalue `2 cos (2πk/15)`. -/
theorem huckel_C15_eigenvector (k : Fin 15) :
    ((cycleGraph 15).adjMatrix ℂ).mulVec (huckelEigenvector k)
        = ((2 * Real.cos (2 * Real.pi * k.val / 15) : ℝ) : ℂ) • huckelEigenvector k ∧
      huckelEigenvector k ≠ 0 :=
  ⟨mulVec_huckelEigenvector k, huckelEigenvector_ne_zero k⟩

end Chem

