import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open Complex Polynomial Matrix

/-- A primitive 15-th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 15)

lemma om_isPrimitiveRoot : IsPrimitiveRoot om 15 := by
  have h := Complex.isPrimitiveRoot_exp 15 (by norm_num)
  simpa [om] using h

lemma om_pow_15 : om ^ (15 : ℕ) = 1 := om_isPrimitiveRoot.pow_eq_one

lemma om_pow_mod (m : ℕ) : om ^ (m % 15) = om ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 15]
  rw [pow_add, pow_mul, om_pow_15, one_pow, one_mul]

/-- The character `j ↦ ω^j` on `Fin 15 ≃ ZMod 15`. -/
noncomputable def zeta (j : Fin 15) : ℂ := om ^ (j : ℕ)

lemma zeta_zero : zeta 0 = 1 := by simp [zeta]

lemma zeta_add (a b : Fin 15) : zeta (a + b) = zeta a * zeta b := by
  simp only [zeta, Fin.val_add, om_pow_mod, pow_add]

lemma zeta_mul (a b : Fin 15) : zeta (a * b) = zeta b ^ (a : ℕ) := by
  simp only [zeta, Fin.val_mul, om_pow_mod, ← pow_mul, mul_comm]

lemma zeta_ne_one {d : Fin 15} (hd : d ≠ 0) : zeta d ≠ 1 := by
  intro h
  have hdvd : (15 : ℕ) ∣ (d : ℕ) := (om_isPrimitiveRoot.pow_eq_one_iff_dvd _).mp h
  have h1 : (d : ℕ) < 15 := d.isLt
  have h2 : (d : ℕ) ≠ 0 := fun h0 => hd (Fin.ext h0)
  omega

lemma sum_zeta (d : Fin 15) :
    (∑ l : Fin 15, zeta (l * d)) = if d = 0 then (15 : ℂ) else 0 := by
  by_cases hd : d = 0
  · subst hd
    simp [zeta]
  · simp only [hd, if_false]
    have hstep : (∑ l : Fin 15, zeta (l * d)) = ∑ i ∈ Finset.range 15, zeta d ^ i := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => zeta d ^ i) 15]
      exact Finset.sum_congr rfl fun l _ => zeta_mul l d
    have hpow : zeta d ^ (15 : ℕ) = 1 := by
      rw [zeta, ← pow_mul, mul_comm, pow_mul, om_pow_15, one_pow]
    have hmul : (∑ i ∈ Finset.range 15, zeta d ^ i) * (zeta d - 1) = 0 := by
      rw [geom_sum_mul, hpow, sub_self]
    have hne : zeta d - 1 ≠ 0 := sub_ne_zero_of_ne (zeta_ne_one hd)
    rw [hstep]
    exact (mul_eq_zero.mp hmul).resolve_right hne

lemma zeta_add_neg (k : Fin 15) :
    zeta k + zeta (-k) = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 15) : ℝ) : ℂ) := by
  set t : ℝ := 2 * Real.pi * (k : ℕ) / 15 with ht
  have h1 : zeta k = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [zeta, om, ← Complex.exp_nat_mul]
    congr 1
    rw [ht]
    push_cast
    ring
  have hmul : zeta k * zeta (-k) = 1 := by
    rw [← zeta_add]
    simp [zeta_zero]
  have h2 : zeta (-k) = Complex.exp (-((t : ℂ) * Complex.I)) := by
    have hk : Complex.exp ((t : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    have hmul' : Complex.exp ((t : ℂ) * Complex.I) * zeta (-k) = 1 := by rw [← h1]; exact hmul
    rw [Complex.exp_neg]
    field_simp
    linear_combination hmul'
  rw [h1, h2, ← neg_mul]
  have hc := Complex.two_cos ((t : ℂ))
  push_cast
  linear_combination -hc

/-- The adjacency matrix of the cycle graph `C₁₅`. -/
noncomputable def adjC15 : Matrix (Fin 15) (Fin 15) ℂ :=
  (SimpleGraph.cycleGraph 15).adjMatrix ℂ

/-- The Hückel eigenvalues `2 cos (2πk/15)`. -/
noncomputable def mu (k : Fin 15) : ℂ := ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 15) : ℝ) : ℂ)

/-- The discrete Fourier transform matrix. -/
noncomputable def dftMat : Matrix (Fin 15) (Fin 15) ℂ := Matrix.of fun j k => zeta (j * k)

/-- Inverse of the discrete Fourier transform matrix. -/
noncomputable def dftInv : Matrix (Fin 15) (Fin 15) ℂ :=
  Matrix.of fun j k => (15 : ℂ)⁻¹ * zeta (-(j * k))

lemma dft_mul_inv : dftMat * dftInv = 1 := by
  ext j k
  rw [Matrix.mul_apply]
  have hterm : ∀ l : Fin 15, dftMat j l * dftInv l k = (15 : ℂ)⁻¹ * zeta (l * (j - k)) := by
    intro l
    simp only [dftMat, dftInv, Matrix.of_apply]
    rw [show l * (j - k) = j * l + -(l * k) by
      rw [mul_sub, sub_eq_add_neg, mul_comm l j], zeta_add]
    ring
  rw [Finset.sum_congr rfl fun l _ => hterm l, ← Finset.mul_sum, sum_zeta]
  by_cases h : j = k
  · subst h
    simp
  · have hjk : j - k ≠ 0 := sub_ne_zero_of_ne h
    simp [hjk, h]

lemma dft_isUnit : IsUnit dftMat := by
  rw [Matrix.isUnit_iff_isUnit_det]
  refine IsUnit.of_mul_eq_one dftInv.det ?_
  rw [← Matrix.det_mul, dft_mul_inv, Matrix.det_one]

lemma sub_one_ne_add_one : ∀ j : Fin 15, j - 1 ≠ j + 1 := by decide

lemma adj_mul_dft : adjC15 * dftMat = dftMat * Matrix.diagonal mu := by
  ext j k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have hsum : (∑ l : Fin 15, adjC15 j l * dftMat l k)
      = ∑ l ∈ (SimpleGraph.cycleGraph 15).neighborFinset j, dftMat l k := by
    have hmv : (∑ l : Fin 15, adjC15 j l * dftMat l k)
        = (((SimpleGraph.cycleGraph 15).adjMatrix ℂ) *ᵥ (fun l => dftMat l k)) j := rfl
    rw [hmv, SimpleGraph.adjMatrix_mulVec_apply]
  rw [hsum, SimpleGraph.cycleGraph_neighborFinset,
    Finset.sum_pair (sub_one_ne_add_one j)]
  simp only [dftMat, Matrix.of_apply, mu]
  rw [show (j - 1) * k = j * k + -k by rw [sub_mul, one_mul, sub_eq_add_neg],
    show (j + 1) * k = j * k + k by rw [add_mul, one_mul],
    zeta_add, zeta_add, ← mul_add, add_comm (zeta (-k)) (zeta k), zeta_add_neg]

lemma charpoly_eq : adjC15.charpoly = ∏ k : Fin 15, (X - C (mu k)) := by
  set U : (Matrix (Fin 15) (Fin 15) ℂ)ˣ := dft_isUnit.unit
  have hU : (U : Matrix (Fin 15) (Fin 15) ℂ) = dftMat := dft_isUnit.unit_spec
  have key : adjC15 = (U : Matrix (Fin 15) (Fin 15) ℂ) * Matrix.diagonal mu
      * ((U⁻¹ : (Matrix (Fin 15) (Fin 15) ℂ)ˣ) : Matrix (Fin 15) (Fin 15) ℂ) := by
    calc adjC15 = adjC15 * ((U : Matrix (Fin 15) (Fin 15) ℂ) * (↑U⁻¹)) := by
          rw [U.mul_inv, mul_one]
      _ = (adjC15 * (U : Matrix (Fin 15) (Fin 15) ℂ)) * (↑U⁻¹) := (mul_assoc _ _ _).symm
      _ = _ := by rw [hU, adj_mul_dft]
  rw [key, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]

/-- **Hückel theory for the C₁₅ cycle.**  The characteristic polynomial of the adjacency
matrix of the cycle graph `C₁₅` factors as `∏ₖ (X - 2cos(2πk/15))`, and consequently the
spectrum of the adjacency matrix is exactly `{2 cos (2πk/15) : k = 0, …, 14}`. -/
theorem huckel_C15 :
    ((SimpleGraph.cycleGraph 15).adjMatrix ℂ).charpoly
        = ∏ k : Fin 15, (X - C ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 15) : ℝ) : ℂ)) ∧
      ∀ z : ℂ, z ∈ spectrum ℂ ((SimpleGraph.cycleGraph 15).adjMatrix ℂ) ↔
        ∃ k : Fin 15, z = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 15) : ℝ) : ℂ) := by
  have hcp : ((SimpleGraph.cycleGraph 15).adjMatrix ℂ).charpoly
      = ∏ k : Fin 15, (X - C (mu k)) := charpoly_eq
  refine ⟨hcp, fun z => ?_⟩
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot, hcp]
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero, mu]

end Chem

