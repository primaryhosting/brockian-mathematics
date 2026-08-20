import RequestProject.SSA.PartialTrace

/-!
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(The header comment above has to follow the `import` line: Lean requires `import` commands to
come first in a file.)

The von Neumann entropy `S(A) = -Tr (A log A)` of a positive definite matrix on a threefold
tensor product `α ⊗ β ⊗ γ` satisfies the Lieb–Ruskai inequality

`S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`.

The proof goes through Lindblad's joint convexity of the Umegaki relative entropy
(itself deduced from Ando's joint concavity of the operator geometric mean) and the
resulting monotonicity of the relative entropy under partial traces.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Kronecker
open Matrix

set_option maxHeartbeats 1000000

namespace QI

variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

/-! ### Relative entropy against `1 ⊗ Y` -/


theorem Qd_eval (hA : A.PosDef) (hB : B.PosDef) (m : ℕ) :
    Qd m A B
      = ∑ i, ∑ j, ovl hA.1 hB.1 i j * dyseq m (hA.1.eigenvalues i) (hB.1.eigenvalues j) := by
  classical
  set U : Matrix n n ℂ := ↑hA.1.eigenvectorUnitary with hUdef
  set V : Matrix n n ℂ := ↑hB.1.eigenvectorUnitary with hVdef
  set lam := hA.1.eigenvalues with hlam
  set mu := hB.1.eigenvalues with hmu
  have hUU : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hA.1.eigenvectorUnitary.2
  have hVV : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hB.1.eigenvectorUnitary.2
  set Vc : Matrix n n ℂ := (Vᴴ)ᵀ with hVcdef
  have hVcH : Vcᴴ = Vᵀ := by
    ext i j
    simp [hVcdef, Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have hVcVt : Vc * Vᵀ = 1 := by
    rw [hVcdef, ← Matrix.transpose_mul, hVV, Matrix.transpose_one]
  set W : Matrix (n × n) (n × n) ℂ := U ⊗ₖ Vc with hWdef
  have hWH : Wᴴ = Uᴴ ⊗ₖ Vᵀ := by rw [hWdef, Matrix.conjTranspose_kronecker, hVcH]
  have hWW : W * Wᴴ = 1 := by
    rw [hWH, hWdef, ← Matrix.mul_kronecker_mul, hUU, hVcVt, Matrix.one_kronecker_one]
  have hWunit : IsUnit W :=
    (Matrix.isUnit_iff_isUnit_det W).2 (Matrix.isUnit_det_of_right_inverse hWW)
  -- spectral decompositions
  have hspecA : A = U * diagonal (fun i => ((lam i : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rw [hA.1.spectral_theorem]
    rfl
  have hspecB : B = V * diagonal (fun j => ((mu j : ℝ) : ℂ)) * Vᴴ := by
    conv_lhs => rw [hB.1.spectral_theorem]
    rfl
  set dl : n × n → ℝ := fun p => lam p.1 with hdl
  set dr : n × n → ℝ := fun p => mu p.2 with hdr
  have hDl : (diagonal fun p => ((dl p : ℝ) : ℂ))
      = (diagonal fun i => ((lam i : ℝ) : ℂ)) ⊗ₖ (1 : Matrix n n ℂ) := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal]
    simp [hdl]
  have hDr : (diagonal fun p => ((dr p : ℝ) : ℂ))
      = (1 : Matrix n n ℂ) ⊗ₖ (diagonal fun j => ((mu j : ℝ) : ℂ)) := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal]
    simp [hdr]
  have hL : liftL A = W * (diagonal fun p => ((dl p : ℝ) : ℂ)) * Wᴴ := by
    have h : W * (diagonal fun p => ((dl p : ℝ) : ℂ)) * Wᴴ
        = (U * diagonal (fun i => ((lam i : ℝ) : ℂ)) * Uᴴ) ⊗ₖ (Vc * 1 * Vᵀ) := by
      rw [hWdef, hWH, hDl, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    rw [h, mul_one, hVcVt, ← hspecA]
    rfl
  have hR : liftR B = W * (diagonal fun p => ((dr p : ℝ) : ℂ)) * Wᴴ := by
    have h : W * (diagonal fun p => ((dr p : ℝ) : ℂ)) * Wᴴ
        = (U * 1 * Uᴴ) ⊗ₖ (Vc * diagonal (fun j => ((mu j : ℝ) : ℂ)) * Vᵀ) := by
      rw [hWdef, hWH, hDr, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    have hBt : Vc * diagonal (fun j => ((mu j : ℝ) : ℂ)) * Vᵀ = Bᵀ := by
      conv_rhs => rw [hspecB]
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose, hVcdef]
      rw [Matrix.mul_assoc]
    rw [h, mul_one, hUU, hBt]
    rfl
  -- positivity of the diagonal data
  have hdlpos : ∀ p, 0 < dl p := fun p => hA.eigenvalues_pos p.1
  have hdrpos : ∀ p, 0 < dr p := fun p => hB.eigenvalues_pos p.2
  have hDlpos : (diagonal fun p => ((dl p : ℝ) : ℂ)).PosDef := by
    rw [Matrix.posDef_diagonal_iff]
    intro p
    exact_mod_cast hdlpos p
  have hDrpsd : (diagonal fun p => ((dr p : ℝ) : ℂ)).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro p
    exact_mod_cast (hdrpos p).le
  have hgpow : gpow m (liftL A) (liftR B)
      = W * (diagonal fun p => ((dyseq m (dl p) (dr p) : ℝ) : ℂ)) * Wᴴ := by
    rw [hL, hR, gpow_congr hDlpos hDrpsd hWunit m, gpow_diagonal hdlpos hdrpos m]
  -- evaluate the quadratic form
  have hnormSq : ∀ i j : n, Complex.normSq (∑ k, W (k, k) (i, j)) = ovl hA.1 hB.1 i j := by
    intro i j
    have hentry : ∀ k : n, W (k, k) (i, j) = U k i * (starRingEnd ℂ) (V k j) := by
      intro k
      simp [hWdef, hVcdef, Matrix.conjTranspose_apply, Matrix.transpose_apply]
    have hsum : (∑ k, W (k, k) (i, j))
        = (starRingEnd ℂ) (((star U : Matrix n n ℂ) * V) i j) := by
      rw [Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hentry k]
      simp [star_eq_conjTranspose, Matrix.conjTranspose_apply, mul_comm]
    rw [hsum, Complex.normSq_conj]
    rfl
  rw [Qd, hgpow, qform_conj_diagonal, Complex.ofReal_re, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hnormSq i j]
  ring

end QI

import RequestProject.SSA.Homs

/-!
# Invariance properties of the relative entropy

The relative entropy is unchanged by conjugation with a unitary and by reindexing the matrix
along an equivalence of index types.  We also record how `CFC.log` interacts with the
embedding `Y ↦ 1 ⊗ Y`.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Kronecker
open Matrix

set_option maxHeartbeats 1000000

namespace QI

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The real logarithm is continuous on the spectrum of a positive definite matrix. -/
