/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Chem

open Matrix Polynomial

/-- A primitive 17-th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 17)

lemma om_isPrimitiveRoot : IsPrimitiveRoot om 17 := by
  simpa [om] using Complex.isPrimitiveRoot_exp 17 (by norm_num)

lemma om_pow_17 : om ^ (17 : ℕ) = 1 := om_isPrimitiveRoot.pow_eq_one

lemma om_pow_mod (a : ℕ) : om ^ (a % 17) = om ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a 17]
  rw [pow_add, pow_mul, om_pow_17, one_pow, one_mul]

/-- The character `Fin 17 → ℂ`, `x ↦ ω ^ x`. -/
noncomputable def zeta (x : Fin 17) : ℂ := om ^ (x : ℕ)

lemma zeta_add (x y : Fin 17) : zeta (x + y) = zeta x * zeta y := by
  simp only [zeta, Fin.val_add, om_pow_mod, pow_add]

lemma zeta_zero : zeta 0 = 1 := by simp [zeta]

lemma zeta_ne_zero (x : Fin 17) : zeta x ≠ 0 :=
  pow_ne_zero _ (Complex.exp_ne_zero _)

lemma zeta_neg (k : Fin 17) : zeta (-k) = (zeta k)⁻¹ := by
  have h : zeta k * zeta (-k) = 1 := by
    rw [← zeta_add]; simp [zeta_zero]
  exact (inv_eq_of_mul_eq_one_right h).symm

lemma zeta_eq_exp (k : Fin 17) :
    zeta k = Complex.exp (((2 * Real.pi * (k : ℕ) / 17 : ℝ) : ℂ) * Complex.I) := by
  rw [zeta, om, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma zeta_add_zeta_neg (k : Fin 17) :
    zeta k + zeta (-k) = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 17) : ℝ) : ℂ) := by
  have h : ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 17) : ℝ) : ℂ)
      = 2 * Complex.cos ((2 * Real.pi * (k : ℕ) / 17 : ℝ) : ℂ) := by
    push_cast [Complex.ofReal_cos]
    ring
  rw [h, Complex.two_cos, zeta_neg, zeta_eq_exp k, ← Complex.exp_neg, neg_mul]

/-- The DFT (Vandermonde) matrix. -/
noncomputable def F17 : Matrix (Fin 17) (Fin 17) ℂ :=
  Matrix.vandermonde (fun j : Fin 17 => om ^ (j : ℕ))

lemma F17_apply (i j : Fin 17) : F17 i j = zeta (i * j) := by
  simp only [F17, Matrix.vandermonde_apply, zeta, Fin.val_mul, om_pow_mod, ← pow_mul]

/-- The diagonal matrix of Hückel eigenvalues of the 17-cycle. -/
noncomputable def D17 : Matrix (Fin 17) (Fin 17) ℂ :=
  Matrix.diagonal (fun k : Fin 17 => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 17) : ℝ) : ℂ))

/-- The adjacency matrix of the cycle graph `C₁₇`. -/
noncomputable def A17 : Matrix (Fin 17) (Fin 17) ℂ := (SimpleGraph.cycleGraph 17).adjMatrix ℂ

lemma fin17_sub_eq_one_iff {i j : Fin 17} : i - j = 1 ↔ j = i - 1 := by
  constructor
  · intro h; rw [← h]; abel
  · intro h; rw [h]; abel

lemma fin17_val_sub_eq_one_iff {i j : Fin 17} : (i - j).val = 1 ↔ j = i - 1 := by
  rw [← fin17_sub_eq_one_iff, Fin.ext_iff]
  simp

lemma A17_apply (i j : Fin 17) :
    A17 i j = (if j = i - 1 then 1 else 0) + (if j = i + 1 then 1 else 0) := by
  have hne : (i - 1 : Fin 17) ≠ i + 1 := by
    intro h
    rw [sub_eq_add_neg] at h
    have h2 : (-1 : Fin 17) = 1 := add_left_cancel h
    exact absurd h2 (by decide)
  have hadj : (SimpleGraph.cycleGraph 17).Adj i j ↔ (j = i - 1 ∨ j = i + 1) := by
    rw [SimpleGraph.cycleGraph_adj', fin17_val_sub_eq_one_iff, fin17_val_sub_eq_one_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · right; rw [h]; abel
    · rintro (h | h)
      · exact Or.inl h
      · right; rw [h]; abel
  rw [A17, SimpleGraph.adjMatrix_apply]
  simp only [hadj]
  by_cases h1 : j = i - 1 <;> by_cases h2 : j = i + 1 <;>
    simp_all

lemma A17_mul_F17 : A17 * F17 = F17 * D17 := by
  ext i k
  have hne : (i - 1 : Fin 17) ≠ i + 1 := by
    intro h
    rw [sub_eq_add_neg] at h
    have h2 : (-1 : Fin 17) = 1 := add_left_cancel h
    exact absurd h2 (by decide)
  rw [Matrix.mul_apply]
  have hsum : ∀ j : Fin 17, A17 i j * F17 j k
      = (if j = i - 1 then F17 j k else 0) + (if j = i + 1 then F17 j k else 0) := by
    intro j
    rw [A17_apply]
    by_cases h1 : j = i - 1 <;> by_cases h2 : j = i + 1 <;>
      simp [h1, h2, hne, Ne.symm hne]
  rw [Finset.sum_congr rfl (fun j _ => hsum j), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (i - 1) (fun j => F17 j k),
    Finset.sum_ite_eq' Finset.univ (i + 1) (fun j => F17 j k)]
  simp only [Finset.mem_univ, if_true]
  rw [D17, Matrix.mul_diagonal, F17_apply, F17_apply, F17_apply, ← zeta_add_zeta_neg]
  have e1 : (i - 1) * k = i * k + (-k) := by rw [sub_mul, one_mul, sub_eq_add_neg]
  have e2 : (i + 1) * k = i * k + k := by rw [add_mul, one_mul]
  rw [e1, e2, zeta_add, zeta_add]
  ring

lemma F17_det_ne_zero : F17.det ≠ 0 := by
  rw [F17, Matrix.det_vandermonde_ne_zero_iff]
  intro i j h
  exact Fin.ext (om_isPrimitiveRoot.pow_inj i.isLt j.isLt h)

lemma F17_isUnit : IsUnit F17 :=
  (Matrix.isUnit_iff_isUnit_det F17).mpr (isUnit_iff_ne_zero.mpr F17_det_ne_zero)

lemma A17_eq_conj : A17 = F17 * D17 * F17⁻¹ := by
  rw [← A17_mul_F17, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr
    F17_det_ne_zero), Matrix.mul_one]

theorem huckel_C17 :
    ((SimpleGraph.cycleGraph 17).adjMatrix ℂ).charpoly =
      ∏ k : Fin 17,
        (X - C (((2 * Real.cos (2 * Real.pi * (k : ℕ) / 17) : ℝ) : ℂ))) := by
  obtain ⟨u, hu⟩ := F17_isUnit
  have hA : ((SimpleGraph.cycleGraph 17).adjMatrix ℂ) = u.val * D17 * u⁻¹.val := by
    rw [← A17, A17_eq_conj, Matrix.coe_units_inv, hu]
  rw [hA, Matrix.charpoly_units_conj, D17, Matrix.charpoly_diagonal]

/-- The spectrum of the adjacency matrix of `C₁₇` is `{2 cos (2πk/17) : k = 0,…,16}`. -/
theorem huckel_C17_spectrum :
    spectrum ℂ ((SimpleGraph.cycleGraph 17).adjMatrix ℂ) =
      Set.range (fun k : Fin 17 => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 17) : ℝ) : ℂ)) := by
  obtain ⟨u, hu⟩ := F17_isUnit
  have hA : ((SimpleGraph.cycleGraph 17).adjMatrix ℂ) = u.val * D17 * u⁻¹.val := by
    rw [← A17, A17_eq_conj, Matrix.coe_units_inv, hu]
  rw [hA, spectrum.units_conjugate, D17, spectrum_diagonal]

end Chem

