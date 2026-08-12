import Mathlib

/-!
# Hückel theory for the cyclic polyene C₁₂

The adjacency eigenvalues of the cycle graph `C₁₂` are `2 * cos (2 * π * k / 12)` for
`k = 0, …, 11`.
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Polynomial Matrix

/-- A primitive 12-th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 12)

lemma om_primitiveRoot : IsPrimitiveRoot om 12 := by
  simpa [om] using Complex.isPrimitiveRoot_exp 12 (by norm_num)

lemma om_pow_twelve : om ^ 12 = 1 := om_primitiveRoot.pow_eq_one

lemma om_pow_mod (m : ℕ) : om ^ (m % 12) = om ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 12]
  rw [pow_add, pow_mul, om_pow_twelve, one_pow, one_mul]

/-- The character `Fin 12 → ℂ`, `a ↦ ω ^ a`. -/
noncomputable def zeta (a : Fin 12) : ℂ := om ^ (a : ℕ)

lemma zeta_add (a b : Fin 12) : zeta (a + b) = zeta a * zeta b := by
  simp only [zeta, Fin.val_add, om_pow_mod, pow_add]

lemma zeta_zero : zeta 0 = 1 := by simp [zeta]

lemma zeta_ne_zero (a : Fin 12) : zeta a ≠ 0 := by
  have : om ≠ 0 := by
    simp [om, Complex.exp_ne_zero]
  exact pow_ne_zero _ this

/-- `ζ k` is the complex exponential `exp ((2πk/12) I)`. -/
lemma zeta_eq_exp (k : Fin 12) :
    zeta k = Complex.exp (((2 * Real.pi * (k : ℕ) / 12 : ℝ) : ℂ) * Complex.I) := by
  rw [zeta, om, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma zeta_neg_mul (k : Fin 12) : zeta k * zeta (-k) = 1 := by
  rw [← zeta_add]
  simp [zeta_zero]

/-- The eigenvalue: `ζ k + ζ (-k) = 2 cos (2πk/12)`. -/
lemma zeta_add_zeta_neg (k : Fin 12) :
    zeta k + zeta (-k) = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 12) : ℝ) : ℂ) := by
  have hinv : zeta (-k) = Complex.exp (-((2 * Real.pi * (k : ℕ) / 12 : ℝ) : ℂ) * Complex.I) := by
    have h := zeta_neg_mul k
    rw [zeta_eq_exp k] at h
    have : Complex.exp (((2 * Real.pi * (k : ℕ) / 12 : ℝ) : ℂ) * Complex.I) *
        Complex.exp (-((2 * Real.pi * (k : ℕ) / 12 : ℝ) : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]
      simp
    have hne : Complex.exp (((2 * Real.pi * (k : ℕ) / 12 : ℝ) : ℂ) * Complex.I) ≠ 0 :=
      Complex.exp_ne_zero _
    field_simp at h this ⊢
    exact mul_left_cancel₀ hne (h.trans this.symm)
  rw [zeta_eq_exp k, hinv, ← Complex.two_cos]
  push_cast
  ring

/-- The (complex) adjacency matrix of the 12-cycle. -/
noncomputable def A12 : Matrix (Fin 12) (Fin 12) ℂ := (SimpleGraph.cycleGraph 12).adjMatrix ℂ

/-- The matrix of characters (a Vandermonde matrix in the powers of `ω`). -/
noncomputable def P12 : Matrix (Fin 12) (Fin 12) ℂ := Matrix.vandermonde (fun j => om ^ (j : ℕ))

/-- The diagonal matrix of eigenvalues. -/
noncomputable def D12 : Matrix (Fin 12) (Fin 12) ℂ :=
  Matrix.diagonal (fun k : Fin 12 => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 12) : ℝ) : ℂ))

lemma P12_apply (i j : Fin 12) : P12 i j = zeta (i * j) := by
  simp only [P12, Matrix.vandermonde_apply, zeta, Fin.val_mul, om_pow_mod, pow_mul]

lemma P12_det_ne_zero : P12.det ≠ 0 := by
  rw [P12, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro i _
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro j hj
  have hij : i < j := Finset.mem_Ioi.mp hj
  have : om ^ (j : ℕ) ≠ om ^ (i : ℕ) := by
    intro h
    have := om_primitiveRoot.pow_inj j.isLt i.isLt h
    exact absurd (Fin.ext this) (ne_of_gt hij)
  exact sub_ne_zero.mpr this

lemma sub_one_ne_add_one (i : Fin 12) : i - 1 ≠ i + 1 := by
  intro h
  rw [sub_eq_add_neg] at h
  exact absurd (add_left_cancel h) (by decide)

/-- The key intertwining relation `A · P = P · D`. -/
lemma A12_mul_P12 : A12 * P12 = P12 * D12 := by
  ext i k
  have hrow : (A12 * P12) i k = ∑ u ∈ (SimpleGraph.cycleGraph 12).neighborFinset i, P12 u k := by
    have h := SimpleGraph.adjMatrix_mulVec_apply (α := ℂ) (SimpleGraph.cycleGraph 12) i
      (fun u => P12 u k)
    simpa [A12, Matrix.mul_apply, Matrix.mulVec, dotProduct] using h
  rw [hrow, SimpleGraph.cycleGraph_neighborFinset, Finset.sum_pair (sub_one_ne_add_one i)]
  rw [P12_apply, P12_apply, D12, Matrix.mul_diagonal, P12_apply]
  have h1 : (i - 1) * k = i * k + (-k) := by rw [sub_mul, one_mul, sub_eq_add_neg]
  have h2 : (i + 1) * k = i * k + k := by rw [add_mul, one_mul]
  rw [h1, h2, zeta_add, zeta_add, ← mul_add, add_comm (zeta (-k)) (zeta k),
    zeta_add_zeta_neg k]

lemma A12_charpoly :
    A12.charpoly =
      ∏ k : Fin 12, (X - C ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 12) : ℝ) : ℂ)) := by
  have hu : IsUnit P12 := (Matrix.isUnit_iff_isUnit_det P12).mpr (isUnit_iff_ne_zero.mpr P12_det_ne_zero)
  obtain ⟨U, hU⟩ := hu
  have hUinv : (↑U⁻¹ : Matrix (Fin 12) (Fin 12) ℂ) = P12⁻¹ := by
    rw [Matrix.coe_units_inv, hU]
  have hA : A12 = (U : Matrix (Fin 12) (Fin 12) ℂ) * D12 * (↑U⁻¹ : Matrix (Fin 12) (Fin 12) ℂ) := by
    rw [hU, hUinv, ← A12_mul_P12, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv P12 (isUnit_iff_ne_zero.mpr P12_det_ne_zero), Matrix.mul_one]
  rw [hA, Matrix.charpoly_units_conj, D12, Matrix.charpoly_diagonal]

lemma adjMatrix_map :
    ((SimpleGraph.cycleGraph 12).adjMatrix ℝ).map (Complex.ofRealHom) = A12 := by
  ext i j
  by_cases h : (SimpleGraph.cycleGraph 12).Adj i j <;>
    simp [A12, SimpleGraph.adjMatrix, h]

/-- The characteristic polynomial of the adjacency matrix of `C₁₂` factors with roots
`2 cos (2πk/12)`. -/
theorem cycleGraph12_charpoly :
    ((SimpleGraph.cycleGraph 12).adjMatrix ℝ).charpoly =
      ∏ k : Fin 12, (X - C (2 * Real.cos (2 * Real.pi * (k : ℕ) / 12))) := by
  refine Polynomial.map_injective (Complex.ofRealHom) Complex.ofReal_injective ?_
  rw [← Matrix.charpoly_map, adjMatrix_map, A12_charpoly, Polynomial.map_prod]
  refine Finset.prod_congr rfl ?_
  intro k _
  simp

/-- **Hückel theory for C₁₂.** The eigenvalues of the adjacency matrix of the cycle graph
`C₁₂` are exactly the numbers `2 cos (2 π k / 12)`, `k = 0, …, 11`. -/
theorem huckel_C12 :
    spectrum ℝ ((SimpleGraph.cycleGraph 12).adjMatrix ℝ) =
      {x : ℝ | ∃ k : Fin 12, x = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 12)} := by
  ext x
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, cycleGraph12_charpoly, Polynomial.IsRoot,
    Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by linarith⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by linarith⟩

end Chem

import RequestProject.Huckel
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

