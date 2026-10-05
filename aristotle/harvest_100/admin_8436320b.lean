import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
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

/-- The Hückel (adjacency) matrix of the cycle graph `C₁₆`, over `ℝ`. -/
noncomputable def huckelMatrix : Matrix (Fin 16) (Fin 16) ℝ :=
  (SimpleGraph.cycleGraph 16).adjMatrix ℝ

/-- The `k`-th Hückel eigenvalue of `C₁₆`, namely `2 cos (2πk/16)`. -/
noncomputable def huckelEigenvalue (k : Fin 16) : ℝ :=
  2 * Real.cos (2 * Real.pi * (k : ℕ) / 16)

/-- A primitive 16-th root of unity. -/
noncomputable def w : ℂ := Complex.exp (2 * Real.pi * Complex.I / 16)

/-- The (unnormalized) discrete Fourier matrix of size 16. -/
noncomputable def dftMatrix : Matrix (Fin 16) (Fin 16) ℂ :=
  Matrix.of fun i k => w ^ ((i : ℕ) * (k : ℕ))

/-- The inverse of the discrete Fourier matrix `dftMatrix`. -/
noncomputable def dftMatrixInv : Matrix (Fin 16) (Fin 16) ℂ :=
  Matrix.of fun k j => (16 : ℂ)⁻¹ * w ^ (15 * ((k : ℕ) * (j : ℕ)))

lemma w_primitive : IsPrimitiveRoot w 16 := by
  have h := Complex.isPrimitiveRoot_exp 16 (by norm_num)
  unfold w
  convert h using 2

lemma w_pow_16 : w ^ 16 = 1 := w_primitive.pow_eq_one

lemma w_pow_mod (a : ℕ) : w ^ (a % 16) = w ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a 16, pow_add, pow_mul, w_pow_16, one_pow, one_mul]

lemma w_pow_congr {a b : ℕ} (h : a % 16 = b % 16) : w ^ a = w ^ b := by
  rw [← w_pow_mod a, ← w_pow_mod b, h]

lemma w_pow_ne_one {m : ℕ} (h : ¬ (16 ∣ m)) : w ^ m ≠ 1 :=
  fun hc => h ((w_primitive.pow_eq_one_iff_dvd m).1 hc)

lemma dvd_iff_eq : ∀ k l : Fin 16, (16 ∣ (15 * (k : ℕ) + (l : ℕ))) ↔ k = l := by decide

lemma dftMatrixInv_mul_dftMatrix : dftMatrixInv * dftMatrix = 1 := by
  ext k l
  rw [Matrix.mul_apply]
  have key : ∀ j : Fin 16, dftMatrixInv k j * dftMatrix j l
      = (16 : ℂ)⁻¹ * (w ^ (15 * (k : ℕ) + (l : ℕ))) ^ (j : ℕ) := by
    intro j
    simp only [dftMatrixInv, dftMatrix, Matrix.of_apply]
    rw [← pow_mul, mul_assoc, ← pow_add]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun j _ => key j), ← Finset.mul_sum]
  set z : ℂ := w ^ (15 * (k : ℕ) + (l : ℕ)) with hz
  by_cases h : k = l
  · subst h
    have h1 : z = 1 := by
      rw [hz]
      exact (w_primitive.pow_eq_one_iff_dvd _).2 ((dvd_iff_eq k k).2 rfl)
    simp [h1]
  · have hzne : z ≠ 1 := by
      rw [hz]
      exact w_pow_ne_one (fun hd => h ((dvd_iff_eq k l).1 hd))
    have hz16 : z ^ 16 = 1 := by
      rw [hz, ← pow_mul]
      exact (w_primitive.pow_eq_one_iff_dvd _).2 ⟨15 * (k : ℕ) + (l : ℕ), by ring⟩
    have hsum : ∑ j : Fin 16, z ^ (j : ℕ) = 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun j => z ^ j) 16, geom_sum_eq hzne, hz16]
      simp
    rw [hsum]
    simp [h]

lemma dftMatrix_mul_dftMatrixInv : dftMatrix * dftMatrixInv = 1 :=
  mul_eq_one_comm.2 dftMatrixInv_mul_dftMatrix

/-- `w ^ k + w ^ (-k)` is the real number `2 cos (2πk/16)`. -/
lemma eigenvalue_eq (k : Fin 16) :
    w ^ (k : ℕ) + w ^ (15 * (k : ℕ)) = (huckelEigenvalue k : ℂ) := by
  set t : ℝ := 2 * Real.pi * (k : ℕ) / 16 with ht
  have hwk : w ^ (k : ℕ) = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [w, ← Complex.exp_nat_mul]
    congr 1
    rw [ht]
    push_cast
    ring
  have hmul : w ^ (k : ℕ) * w ^ (15 * (k : ℕ)) = 1 := by
    rw [← pow_add]
    have h16 : (k : ℕ) + 15 * (k : ℕ) = 16 * (k : ℕ) := by ring
    rw [h16, pow_mul, w_pow_16, one_pow]
  have hne : w ^ (k : ℕ) ≠ 0 := by
    rw [hwk]; exact Complex.exp_ne_zero _
  have hinv : w ^ (15 * (k : ℕ)) = Complex.exp (-(t : ℂ) * Complex.I) := by
    have hQ : w ^ (15 * (k : ℕ)) = (w ^ (k : ℕ))⁻¹ := by
      field_simp at hmul ⊢
      linear_combination hmul
    rw [hQ, hwk, ← Complex.exp_neg]
    ring_nf
  rw [hwk, hinv, ← Complex.two_cos, huckelEigenvalue, ← ht]
  push_cast
  ring

lemma cycle_sub_one : ∀ i : Fin 16, i - 1 = i + 15 := by decide

lemma cycle_neighbors_ne : ∀ i : Fin 16, i - 1 ≠ i + 1 := by decide

lemma w_shift (i c k : Fin 16) :
    w ^ (((i + c : Fin 16) : ℕ) * (k : ℕ))
      = w ^ ((i : ℕ) * (k : ℕ)) * w ^ ((c : ℕ) * (k : ℕ)) := by
  rw [← pow_add]
  apply w_pow_congr
  rw [Fin.val_add]
  calc (((i : ℕ) + (c : ℕ)) % 16 * (k : ℕ)) % 16
      = (((i : ℕ) + (c : ℕ)) * (k : ℕ)) % 16 := (Nat.mod_modEq _ 16).mul_right _
    _ = ((i : ℕ) * (k : ℕ) + (c : ℕ) * (k : ℕ)) % 16 := by ring_nf

/-- The Fourier matrix diagonalizes the adjacency matrix of `C₁₆`. -/
lemma adj_mul_dftMatrix :
    ((SimpleGraph.cycleGraph 16).adjMatrix ℂ) * dftMatrix
      = dftMatrix * Matrix.diagonal (fun k => (huckelEigenvalue k : ℂ)) := by
  ext i k
  have h1 : (((SimpleGraph.cycleGraph 16).adjMatrix ℂ) * dftMatrix) i k
      = (((SimpleGraph.cycleGraph 16).adjMatrix ℂ) *ᵥ (fun j => dftMatrix j k)) i := rfl
  rw [h1, SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.cycleGraph_neighborFinset,
    Finset.sum_pair (cycle_neighbors_ne i), Matrix.mul_diagonal, cycle_sub_one i]
  show w ^ (((i + 15 : Fin 16) : ℕ) * (k : ℕ)) + w ^ (((i + 1 : Fin 16) : ℕ) * (k : ℕ))
      = w ^ ((i : ℕ) * (k : ℕ)) * (huckelEigenvalue k : ℂ)
  rw [w_shift i 15 k, w_shift i 1 k, ← eigenvalue_eq k]
  show _ + _ = w ^ ((i : ℕ) * (k : ℕ)) * (w ^ (k : ℕ) + w ^ (15 * (k : ℕ)))
  have h15 : ((15 : Fin 16) : ℕ) = 15 := rfl
  have h11 : ((1 : Fin 16) : ℕ) = 1 := rfl
  rw [h15, h11, one_mul]
  ring

/-- The characteristic polynomial of the complex adjacency matrix of `C₁₆`. -/
lemma charpoly_complex :
    ((SimpleGraph.cycleGraph 16).adjMatrix ℂ).charpoly
      = ∏ k : Fin 16, (X - C (huckelEigenvalue k : ℂ)) := by
  set u : (Matrix (Fin 16) (Fin 16) ℂ)ˣ :=
    ⟨dftMatrix, dftMatrixInv, dftMatrix_mul_dftMatrixInv, dftMatrixInv_mul_dftMatrix⟩ with hu
  have hconj : ((SimpleGraph.cycleGraph 16).adjMatrix ℂ)
      = (u : Matrix (Fin 16) (Fin 16) ℂ)
        * Matrix.diagonal (fun k => (huckelEigenvalue k : ℂ))
        * ((u⁻¹ : (Matrix (Fin 16) (Fin 16) ℂ)ˣ) : Matrix (Fin 16) (Fin 16) ℂ) := by
    have h := adj_mul_dftMatrix
    have : ((SimpleGraph.cycleGraph 16).adjMatrix ℂ) * dftMatrix * dftMatrixInv
        = dftMatrix * Matrix.diagonal (fun k => (huckelEigenvalue k : ℂ)) * dftMatrixInv := by
      rw [h]
    rwa [mul_assoc, dftMatrix_mul_dftMatrixInv, mul_one] at this
  rw [hconj, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]

lemma adjMatrix_map :
    (huckelMatrix.map (Complex.ofRealHom : ℝ →+* ℂ))
      = (SimpleGraph.cycleGraph 16).adjMatrix ℂ := by
  ext i j
  simp [huckelMatrix, Matrix.map_apply, SimpleGraph.adjMatrix_apply, apply_ite]

/-- The characteristic polynomial of the Hückel matrix of `C₁₆` factors into linear factors
with roots `2 cos (2πk/16)`. -/
theorem huckel_C16_charpoly :
    huckelMatrix.charpoly = ∏ k : Fin 16, (X - C (huckelEigenvalue k)) := by
  apply Polynomial.map_injective (Complex.ofRealHom : ℝ →+* ℂ) Complex.ofReal_injective
  rw [← Matrix.charpoly_map, adjMatrix_map, charpoly_complex, Polynomial.map_prod]
  simp

/-- **Hückel theory for the C₁₆ annulene.**  The characteristic polynomial of the adjacency
(Hückel) matrix of the cycle graph `C₁₆` factors completely as `∏_{k=0}^{15} (X - 2cos(2πk/16))`;
consequently the set of adjacency eigenvalues of `C₁₆` is exactly
`{2 cos (2πk/16) : k = 0, …, 15}`. -/
theorem huckel_C16 :
    huckelMatrix.charpoly = ∏ k : Fin 16, (X - C (huckelEigenvalue k)) ∧
      spectrum ℝ huckelMatrix = {μ : ℝ | ∃ k : Fin 16, μ = huckelEigenvalue k} := by
  refine ⟨huckel_C16_charpoly, ?_⟩
  ext μ
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C16_charpoly]
  simp only [Polynomial.IsRoot, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Set.mem_setOf_eq]
  rw [Finset.prod_eq_zero_iff]
  simp [sub_eq_zero]

end Chem

#print axioms Chem.huckel_C16

