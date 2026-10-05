import Mathlib

/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace Chem

open Complex SimpleGraph Matrix

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

lemma zeta_ne_zero (n : ℕ) : zeta n ≠ 0 := Complex.exp_ne_zero _

lemma isPrimitiveRoot_zeta {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (zeta n) n :=
  Complex.isPrimitiveRoot_exp n hn

lemma zeta_pow_modEq {n a b : ℕ} (hn : n ≠ 0) (h : a ≡ b [MOD n]) :
    zeta n ^ a = zeta n ^ b :=
  pow_eq_pow_of_modEq h (isPrimitiveRoot_zeta hn).pow_eq_one

/-- The `k`-th power of `zeta n` written as a complex exponential of a real angle. -/
lemma zeta_pow_eq_exp {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    zeta n ^ k = Complex.exp (((2 * Real.pi * k / n : ℝ) : ℂ) * Complex.I) := by
  have hn' : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- `ζ^k + ζ^{-k} = 2 cos(2πk/n)`: the Hückel energy level. -/
lemma zeta_pow_add_inv {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    zeta n ^ k + (zeta n ^ k)⁻¹ = ((2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ) := by
  rw [zeta_pow_eq_exp hn k, ← Complex.exp_neg]
  push_cast
  rw [Complex.cos, neg_mul]
  ring

/-- The (unnormalized) discrete Fourier matrix: `F j k = ζ^(jk)`. -/
noncomputable def dftMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.vandermonde (fun j : Fin n => zeta n ^ (j : ℕ))

lemma dftMatrix_apply {n : ℕ} (j k : Fin n) :
    dftMatrix n j k = zeta n ^ ((j : ℕ) * (k : ℕ)) := by
  rw [dftMatrix, Matrix.vandermonde_apply, ← pow_mul]

lemma dftMatrix_det_ne_zero {n : ℕ} (hn : n ≠ 0) : (dftMatrix n).det ≠ 0 := by
  rw [dftMatrix, Matrix.det_vandermonde_ne_zero_iff]
  intro a b hab
  exact Fin.ext ((isPrimitiveRoot_zeta hn).pow_inj a.isLt b.isLt hab)

/-- The diagonal matrix of Hückel energies `2 cos (2πk/n)`. -/
noncomputable def huckelDiag (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun k : Fin n => ((2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ))

lemma succ_val_modEq {N : ℕ} (j : Fin (N + 2)) :
    ((j + 1 : Fin (N + 2)) : ℕ) ≡ (j : ℕ) + 1 [MOD (N + 2)] := by
  rw [Fin.val_add, Fin.val_one]
  exact Nat.mod_modEq _ _

lemma pred_val_modEq {N : ℕ} (j : Fin (N + 2)) :
    ((j - 1 : Fin (N + 2)) : ℕ) + 1 ≡ (j : ℕ) [MOD (N + 2)] := by
  have h : ((j - 1 : Fin (N + 2)) + 1 : Fin (N + 2)) = j := by
    rw [sub_add_cancel]
  have := congrArg Fin.val h
  rw [Fin.val_add, Fin.val_one] at this
  calc ((j - 1 : Fin (N + 2)) : ℕ) + 1
      ≡ (((j - 1 : Fin (N + 2)) : ℕ) + 1) % (N + 2) [MOD (N + 2)] := (Nat.mod_modEq _ _).symm
    _ = (j : ℕ) := this

lemma pred_ne_succ {N : ℕ} (j : Fin (N + 3)) : (j - 1 : Fin (N + 3)) ≠ j + 1 := by
  intro h
  rw [sub_eq_iff_eq_add, add_assoc] at h
  have h2 : ((1 : Fin (N + 3)) + 1) = 0 := left_eq_add.mp h
  have : ((1 : Fin (N + 3)) + 1 : Fin (N + 3)).val = 0 := by rw [h2]; rfl
  rw [Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt (by omega : 1 + 1 < N + 3)] at this
  omega

/-- Key computation: the adjacency matrix acts on the Fourier basis diagonally. -/
lemma adjMatrix_mul_dftMatrix {N : ℕ} :
    (SimpleGraph.cycleGraph (N + 3)).adjMatrix ℂ * dftMatrix (N + 3)
      = dftMatrix (N + 3) * huckelDiag (N + 3) := by
  have hn : (N + 3) ≠ 0 := by omega
  ext j k
  rw [SimpleGraph.adjMatrix_mul_apply, SimpleGraph.cycleGraph_neighborFinset,
    Finset.sum_pair (pred_ne_succ j), huckelDiag, Matrix.mul_diagonal]
  set z : ℂ := zeta (N + 3) ^ ((j : ℕ) * (k : ℕ)) with hz
  set c : ℂ := zeta (N + 3) ^ (k : ℕ) with hc
  have hcne : c ≠ 0 := pow_ne_zero _ (zeta_ne_zero _)
  have hsucc : dftMatrix (N + 3) (j + 1) k = z * c := by
    rw [dftMatrix_apply, hz, hc, ← pow_add]
    exact zeta_pow_modEq hn
      (((succ_val_modEq (N := N + 1) j).mul_right (k : ℕ)).trans (by rw [add_mul, one_mul]))
  have hpred : dftMatrix (N + 3) (j - 1) k = z * c⁻¹ := by
    have hmul : dftMatrix (N + 3) (j - 1) k * c = z := by
      rw [dftMatrix_apply, hz, hc, ← pow_add]
      refine zeta_pow_modEq hn ?_
      simpa [add_mul] using (pred_val_modEq (N := N + 1) j).mul_right (k : ℕ)
    rw [← hmul]
    field_simp
  rw [hpred, hsucc, dftMatrix_apply, ← hz]
  rw [← zeta_pow_add_inv hn (k : ℕ), ← hc]
  ring

/-- **Hückel cycle spectrum.**  The adjacency (Hückel) eigenvalues of the cycle graph `Cₙ`
(`n ≥ 3`) are exactly the numbers `2 cos (2πk/n)` for `k = 0, …, n-1`. -/
theorem huckel_cycle_spectrum (n : ℕ) (hn : 3 ≤ n) :
    spectrum ℂ ((SimpleGraph.cycleGraph n).adjMatrix ℂ) =
      Set.range (fun k : Fin n => ((2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ)) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 3 := ⟨n - 3, by omega⟩
  have hne : (N + 3) ≠ 0 := by omega
  obtain ⟨u, hu⟩ : IsUnit (dftMatrix (N + 3)) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (dftMatrix_det_ne_zero hne))
  have hAF : (SimpleGraph.cycleGraph (N + 3)).adjMatrix ℂ * dftMatrix (N + 3)
      = dftMatrix (N + 3) * huckelDiag (N + 3) := adjMatrix_mul_dftMatrix
  have key : (SimpleGraph.cycleGraph (N + 3)).adjMatrix ℂ
      = (u : Matrix (Fin (N + 3)) (Fin (N + 3)) ℂ) * huckelDiag (N + 3)
        * ((u⁻¹ : (Matrix (Fin (N + 3)) (Fin (N + 3)) ℂ)ˣ) :
            Matrix (Fin (N + 3)) (Fin (N + 3)) ℂ) := by
    rw [hu, ← hAF, mul_assoc, ← hu, Units.mul_inv, mul_one]
  rw [key, spectrum.units_conjugate, huckelDiag, spectrum_diagonal]

/-- The Hückel molecular orbital with coefficients `c_j = ζ^{jk}` is an eigenvector of the
adjacency matrix of `Cₙ` with eigenvalue `2 cos (2πk/n)`. -/
theorem huckel_cycle_eigenvector (n : ℕ) (hn : 3 ≤ n) (k : Fin n) :
    (SimpleGraph.cycleGraph n).adjMatrix ℂ *ᵥ (fun j : Fin n => zeta n ^ ((j : ℕ) * (k : ℕ)))
      = ((2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ) •
          (fun j : Fin n => zeta n ^ ((j : ℕ) * (k : ℕ))) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 3 := ⟨n - 3, by omega⟩
  funext j
  have hj := congrFun (congrFun (adjMatrix_mul_dftMatrix (N := N)) j) k
  rw [Matrix.mul_apply, huckelDiag, Matrix.mul_diagonal] at hj
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, ← dftMatrix_apply]
  rw [hj]
  ring

/-- The Hückel eigenvectors are nonzero, so the numbers `2 cos (2πk/n)` really are eigenvalues. -/
theorem huckel_cycle_eigenvector_ne_zero (n : ℕ) (hn : 3 ≤ n) (k : Fin n) :
    (fun j : Fin n => zeta n ^ ((j : ℕ) * (k : ℕ))) ≠ 0 := by
  intro h
  have h0 := congrFun h ⟨0, by omega⟩
  simp at h0

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

