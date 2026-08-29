/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
The Hückel (tight-binding) spectrum of the annulene `C₁₅`: the eigenvalues of the
adjacency matrix of the cycle graph `C₁₅` are exactly `2 cos (2πk/15)`, `k = 0, …, 14`.

Mathlib has the cycle graph (`SimpleGraph.cycleGraph`) and its adjacency matrix
(`SimpleGraph.adjMatrix`), the spectrum of a diagonal matrix (`spectrum_diagonal`) and
invariance of the spectrum under conjugation (`spectrum.units_conjugate`), but no
diagonalization of circulant matrices, so we build the discrete Fourier transform
matrix explicitly.
-/

namespace Chem

open Complex Matrix SimpleGraph

noncomputable section

/-- A primitive 15-th root of unity. -/
def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 15)

lemma isPrimitiveRoot_zeta : IsPrimitiveRoot zeta 15 := by
  have h := Complex.isPrimitiveRoot_exp 15 (by norm_num)
  norm_num at h
  simpa [zeta] using h

lemma zeta_pow_15 : zeta ^ 15 = 1 := isPrimitiveRoot_zeta.pow_eq_one

lemma zeta_ne_zero : zeta ≠ 0 := by
  intro h
  have h15 := zeta_pow_15
  rw [h] at h15
  norm_num at h15

lemma zeta_pow_pow_15 (m : ℕ) : (zeta ^ m) ^ 15 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, zeta_pow_15, one_pow]

/-- Geometric sum of a 15-th root of unity over `Fin 15`. -/
lemma geom15 (z : ℂ) (hz : z ^ 15 = 1) :
    ∑ k : Fin 15, z ^ (k : ℕ) = if z = 1 then 15 else 0 := by
  by_cases h : z = 1
  · simp [h]
  · rw [if_neg h, Fin.sum_univ_eq_sum_range (fun k => z ^ k) 15,
      geom_sum_eq h, hz, sub_self, zero_div]

/-- The discrete Fourier transform matrix for `C₁₅`. -/
def Pmat : Matrix (Fin 15) (Fin 15) ℂ := Matrix.of fun j k => zeta ^ ((j : ℕ) * (k : ℕ))

/-- The inverse of the discrete Fourier transform matrix. -/
def Qmat : Matrix (Fin 15) (Fin 15) ℂ :=
  Matrix.of fun j k => (15 : ℂ)⁻¹ * (zeta ^ ((j : ℕ) * (k : ℕ)))⁻¹

/-- Orthogonality of the characters of `ZMod 15`. -/
lemma orthsum (a b : Fin 15) :
    ∑ k : Fin 15, ((zeta ^ (a : ℕ)) * (zeta ^ (b : ℕ))⁻¹) ^ (k : ℕ) =
      if a = b then 15 else 0 := by
  have hz : ((zeta ^ (a : ℕ)) * (zeta ^ (b : ℕ))⁻¹) ^ 15 = 1 := by
    rw [mul_pow, inv_pow, zeta_pow_pow_15, zeta_pow_pow_15, inv_one, mul_one]
  rw [geom15 _ hz]
  congr 1
  simp only [eq_iff_iff]
  rw [mul_inv_eq_one₀ (pow_ne_zero _ zeta_ne_zero)]
  constructor
  · intro h
    exact Fin.ext (isPrimitiveRoot_zeta.pow_inj a.isLt b.isLt h)
  · rintro rfl
    rfl

lemma Pmat_mul_Qmat : Pmat * Qmat = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have key : ∀ k : Fin 15, Pmat j k * Qmat k l
      = (15 : ℂ)⁻¹ * ((zeta ^ (j : ℕ)) * (zeta ^ (l : ℕ))⁻¹) ^ (k : ℕ) := by
    intro k
    have expand : ((zeta ^ (j : ℕ)) * (zeta ^ (l : ℕ))⁻¹) ^ (k : ℕ)
        = zeta ^ ((j : ℕ) * (k : ℕ)) * (zeta ^ ((k : ℕ) * (l : ℕ)))⁻¹ := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm (l : ℕ) (k : ℕ)]
    simp only [Pmat, Qmat, Matrix.of_apply]
    rw [expand]
    ring
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.mul_sum, orthsum]
  by_cases h : j = l
  · subst h
    simp
  · rw [if_neg h, Matrix.one_apply_ne h, mul_zero]

lemma Qmat_mul_Pmat : Qmat * Pmat = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have key : ∀ k : Fin 15, Qmat j k * Pmat k l
      = (15 : ℂ)⁻¹ * ((zeta ^ (l : ℕ)) * (zeta ^ (j : ℕ))⁻¹) ^ (k : ℕ) := by
    intro k
    have expand : ((zeta ^ (l : ℕ)) * (zeta ^ (j : ℕ))⁻¹) ^ (k : ℕ)
        = zeta ^ ((k : ℕ) * (l : ℕ)) * (zeta ^ ((j : ℕ) * (k : ℕ)))⁻¹ := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm (l : ℕ) (k : ℕ)]
    simp only [Pmat, Qmat, Matrix.of_apply]
    rw [expand]
    ring
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.mul_sum, orthsum]
  by_cases h : j = l
  · subst h
    simp
  · rw [if_neg (Ne.symm h), Matrix.one_apply_ne h, mul_zero]

/-- The Hückel eigenvalue function `k ↦ 2 cos (2πk/15)`. -/
def hueckelEval (k : Fin 15) : ℂ := 2 * Real.cos (2 * Real.pi * (k : ℕ) / 15)

/-- `ζ ^ k + (ζ ^ k)⁻¹ = 2 cos (2πk/15)`. -/
lemma zeta_pow_add_inv (k : Fin 15) :
    zeta ^ (k : ℕ) + (zeta ^ (k : ℕ))⁻¹ = hueckelEval k := by
  have hzk : zeta ^ (k : ℕ)
      = Complex.exp (((2 * Real.pi * (k : ℕ) / 15 : ℝ) : ℂ) * Complex.I) := by
    rw [zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hzk, ← Complex.exp_neg, hueckelEval, Complex.ofReal_cos, Complex.cos, neg_mul]
  ring

/-- Periodicity: for a 15-th root of unity `w`, the map `a ↦ w ^ a.val` is a
homomorphism from `Fin 15`. -/
lemma pow_val_add (w : ℂ) (hw : w ^ 15 = 1) (a b : Fin 15) :
    w ^ ((a + b : Fin 15) : ℕ) = w ^ (a : ℕ) * w ^ (b : ℕ) := by
  have hmod : ∀ x : ℕ, w ^ (x % 15) = w ^ x := by
    intro x
    conv_rhs => rw [← Nat.div_add_mod x 15]
    rw [pow_add, pow_mul, hw, one_pow, one_mul]
  rw [Fin.val_add, hmod, pow_add]

/-- The columns of the Fourier matrix are eigenvectors of the adjacency matrix. -/
lemma adj_mul_Pmat :
    (SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 15)) * Pmat
      = Pmat * Matrix.diagonal hueckelEval := by
  ext i k
  rw [SimpleGraph.adjMatrix_mul_apply, Matrix.mul_diagonal]
  have hnb : (SimpleGraph.cycleGraph 15).neighborFinset i = {i - 1, i + 1} :=
    SimpleGraph.cycleGraph_neighborFinset
  have hne : ∀ m : Fin 15, m - 1 ≠ m + 1 := by decide
  rw [hnb, Finset.sum_pair (hne i)]
  set w : ℂ := zeta ^ (k : ℕ) with hwdef
  have hw15 : w ^ 15 = 1 := by rw [hwdef]; exact zeta_pow_pow_15 _
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw15; norm_num at hw15
  have hval : ∀ m : Fin 15, Pmat m k = w ^ (m : ℕ) := by
    intro m
    simp only [Pmat, Matrix.of_apply, hwdef, ← pow_mul, mul_comm]
  have hone : ((1 : Fin 15) : ℕ) = 1 := rfl
  have hplus : Pmat (i + 1) k = w ^ (i : ℕ) * w := by
    rw [hval, pow_val_add w hw15, hone, pow_one]
  have hminus : Pmat (i - 1) k = w ^ (i : ℕ) * w⁻¹ := by
    have h1 : (i - 1) + 1 = i := sub_add_cancel i 1
    have h2 := pow_val_add w hw15 (i - 1) 1
    rw [h1, hone, pow_one] at h2
    rw [hval, h2]
    field_simp
  rw [hplus, hminus, hval, ← zeta_pow_add_inv k, ← hwdef]
  ring

/-- **Hückel theory for C₁₅.** The adjacency eigenvalues of the cycle graph `C₁₅`
are exactly `2 cos (2πk/15)` for `k = 0, …, 14`. -/
theorem huckel_C15 :
    spectrum ℂ (SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 15))
      = {μ : ℂ | ∃ k : ℕ, k < 15 ∧ μ = 2 * Real.cos (2 * Real.pi * k / 15)} := by
  set u : (Matrix (Fin 15) (Fin 15) ℂ)ˣ :=
    ⟨Pmat, Qmat, Pmat_mul_Qmat, Qmat_mul_Pmat⟩ with hu
  have hA : SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 15)
      = (u : Matrix (Fin 15) (Fin 15) ℂ) * Matrix.diagonal hueckelEval
        * ((u⁻¹ : (Matrix (Fin 15) (Fin 15) ℂ)ˣ) : Matrix (Fin 15) (Fin 15) ℂ) := by
    show _ = Pmat * Matrix.diagonal hueckelEval * Qmat
    rw [← adj_mul_Pmat, mul_assoc, Pmat_mul_Qmat, mul_one]
  rw [hA, spectrum.units_conjugate, spectrum_diagonal]
  ext μ
  simp only [Set.mem_range, Set.mem_setOf_eq, hueckelEval]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨(k : ℕ), k.isLt, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩

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

