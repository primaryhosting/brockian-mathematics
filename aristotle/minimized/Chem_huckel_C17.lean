import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Chem

open Polynomial Matrix SimpleGraph

/-- A primitive 17-th root of unity. -/

noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 17)

lemma zeta_ne_zero : zeta ≠ 0 := Complex.exp_ne_zero _

lemma zeta_isPrimitiveRoot : IsPrimitiveRoot zeta 17 := by
  have := Complex.isPrimitiveRoot_exp 17 (by norm_num)
  simpa [zeta] using this

lemma zeta_pow_17 : zeta ^ 17 = 1 := zeta_isPrimitiveRoot.pow_eq_one

lemma zeta_pow_mod (a : ℕ) : zeta ^ a = zeta ^ (a % 17) := by
  conv_lhs => rw [← Nat.div_add_mod a 17]
  rw [pow_add, pow_mul, zeta_pow_17, one_pow, one_mul]

lemma zeta_pow_congr {a b : ℕ} (h : a ≡ b [MOD 17]) : zeta ^ a = zeta ^ b := by
  rw [zeta_pow_mod a, zeta_pow_mod b, h]

/-- The DFT (Vandermonde) matrix built from `zeta`. -/

noncomputable def Fmat : Matrix (Fin 17) (Fin 17) ℂ :=
  Matrix.of fun j k => zeta ^ (j.val * k.val)

/-- The eigenvalues `2 cos (2πk/17)`. -/

noncomputable def lam (k : Fin 17) : ℝ := 2 * Real.cos (2 * Real.pi * k.val / 17)

lemma zeta_pow_eq_exp (m : ℕ) :
    zeta ^ m = Complex.exp ((2 * Real.pi * m / 17 : ℝ) * Complex.I) := by
  rw [zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma lam_eq (k : Fin 17) : ((lam k : ℝ) : ℂ) = zeta ^ k.val + zeta ^ (16 * k.val) := by
  have h16 : zeta ^ (16 * k.val) = (zeta ^ k.val)⁻¹ := by
    have hz : zeta ^ k.val ≠ 0 := pow_ne_zero _ zeta_ne_zero
    have : zeta ^ (16 * k.val) * zeta ^ k.val = 1 := by
      rw [← pow_add]
      have : 16 * k.val + k.val = 17 * k.val := by ring
      rw [this, pow_mul, zeta_pow_17, one_pow]
    field_simp at this ⊢
    linear_combination this
  rw [h16, zeta_pow_eq_exp, ← Complex.exp_neg]
  rw [lam]
  push_cast
  rw [Complex.two_cos]
  congr 2
  ring

lemma Fmat_apply (j k : Fin 17) : Fmat j k = zeta ^ (j.val * k.val) := rfl

lemma Fin17_sub_one_ne_add_one (j : Fin 17) : j - 1 ≠ j + 1 := by revert j; decide

lemma adjMatrix_mul_Fmat :
    ((cycleGraph 17).adjMatrix ℂ) * Fmat
      = Fmat * Matrix.diagonal (fun k => ((lam k : ℝ) : ℂ)) := by
  ext j k
  have hlhs : (((cycleGraph 17).adjMatrix ℂ) * Fmat) j k
      = ∑ u ∈ (cycleGraph 17).neighborFinset j, Fmat u k := by
    rw [Matrix.mul_apply]
    exact (SimpleGraph.adjMatrix_mulVec_apply (α := ℂ) (cycleGraph 17) j (fun m => Fmat m k))
  have hnb : (cycleGraph 17).neighborFinset j = {j - 1, j + 1} :=
    SimpleGraph.cycleGraph_neighborFinset (n := 15) (v := j)
  have hne : j - 1 ≠ j + 1 := Fin17_sub_one_ne_add_one j
  rw [hlhs, hnb, Finset.sum_pair hne, Matrix.mul_diagonal, lam_eq]
  -- compute the two shifted entries
  have hsub : ((j - 1 : Fin 17)).val = (j.val + 16) % 17 := by
    rw [Fin.sub_def]
    show (17 - (1 : Fin 17).val + j.val) % 17 = (j.val + 16) % 17
    norm_num
    omega
  have hadd : ((j + 1 : Fin 17)).val = (j.val + 1) % 17 := by
    rw [Fin.add_def]
    show (j.val + (1 : Fin 17).val) % 17 = (j.val + 1) % 17
    norm_num
  have e1 : Fmat (j - 1) k = zeta ^ (j.val * k.val + 16 * k.val) := by
    rw [Fmat_apply, hsub]
    refine zeta_pow_congr ?_
    have h := (Nat.mod_modEq (j.val + 16) 17).mul_right k.val
    calc (j.val + 16) % 17 * k.val ≡ (j.val + 16) * k.val [MOD 17] := h
      _ = j.val * k.val + 16 * k.val := by ring
  have e2 : Fmat (j + 1) k = zeta ^ (j.val * k.val + k.val) := by
    rw [Fmat_apply, hadd]
    refine zeta_pow_congr ?_
    have h := (Nat.mod_modEq (j.val + 1) 17).mul_right k.val
    calc (j.val + 1) % 17 * k.val ≡ (j.val + 1) * k.val [MOD 17] := h
      _ = j.val * k.val + k.val := by ring
  rw [e1, e2, Fmat_apply, pow_add, pow_add]
  ring

lemma Fmat_eq_vandermonde : Fmat = Matrix.vandermonde (fun j : Fin 17 => zeta ^ j.val) := by
  ext j k
  rw [Fmat_apply, Matrix.vandermonde, Matrix.of_apply, ← pow_mul]

lemma Fmat_det_ne_zero : Fmat.det ≠ 0 := by
  rw [Fmat_eq_vandermonde]
  rw [Matrix.det_vandermonde_ne_zero_iff]
  intro a b hab
  have := zeta_isPrimitiveRoot.pow_inj a.isLt b.isLt hab
  exact Fin.ext this

theorem huckel_C17_complex :
    ((cycleGraph 17).adjMatrix ℂ).charpoly
      = ∏ k : Fin 17, (X - C ((lam k : ℝ) : ℂ)) := by
  have hunit : IsUnit Fmat := (Matrix.isUnit_iff_isUnit_det Fmat).2 (Ne.isUnit Fmat_det_ne_zero)
  set u := hunit.unit with hu
  have hA : ((cycleGraph 17).adjMatrix ℂ)
      = u.val * Matrix.diagonal (fun k => ((lam k : ℝ) : ℂ)) * (u⁻¹ : (Matrix (Fin 17) (Fin 17) ℂ)ˣ).val := by
    have hval : (u : Matrix (Fin 17) (Fin 17) ℂ) = Fmat := hunit.unit_spec
    rw [hval, Matrix.coe_units_inv, ← hunit.unit_spec, hval, ← adjMatrix_mul_Fmat,
      Matrix.mul_nonsing_inv_cancel_right _ _ (Ne.isUnit Fmat_det_ne_zero)]
  rw [hA, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]
