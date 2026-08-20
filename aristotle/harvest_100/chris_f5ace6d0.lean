/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
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

open Complex Matrix

/-- The primitive 14-th root of unity `exp(2πi/14)`. -/
noncomputable def om : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 14)

/-- The Hückel eigenvalues `2 cos (2πk/14)`. -/
noncomputable def eigval (k : Fin 14) : ℂ := ((2 * Real.cos (2 * Real.pi * k.val / 14) : ℝ) : ℂ)

/-- The (Vandermonde/DFT) matrix diagonalizing the adjacency matrix of `C₁₄`. -/
noncomputable def dftMat : Matrix (Fin 14) (Fin 14) ℂ :=
  Matrix.vandermonde (fun j : Fin 14 => om ^ (j : ℕ))

lemma om_prim : IsPrimitiveRoot om 14 := by
  have h := Complex.isPrimitiveRoot_exp 14 (by norm_num)
  have h14 : ((14 : ℕ) : ℂ) = (14 : ℂ) := by norm_num
  simpa [om, h14] using h

lemma om_ne_zero : om ≠ 0 := Complex.exp_ne_zero _

lemma om_pow14 : om ^ (14 : ℕ) = 1 := om_prim.pow_eq_one

lemma om_zpow_eq {a b : ℤ} (h : (14 : ℤ) ∣ a - b) : om ^ a = om ^ b := by
  obtain ⟨c, hc⟩ := h
  have ha : a = b + 14 * c := by linarith
  have h14 : om ^ (14 : ℤ) = 1 := by
    rw [show (14 : ℤ) = ((14 : ℕ) : ℤ) by norm_num, zpow_natCast, om_pow14]
  rw [ha, zpow_add₀ om_ne_zero, _root_.zpow_mul, h14, _root_.one_zpow, mul_one]

/-- The Hückel eigenvalue `2 cos (2πk/14)` as a sum of two powers of `om`. -/
lemma eigval_eq (k : Fin 14) :
    eigval k = om ^ ((k.val : ℤ)) + om ^ (-(k.val : ℤ)) := by
  have h1 : ((2 * Real.pi * k.val / 14 : ℝ) : ℂ) * Complex.I
      = ((k.val : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 14) := by push_cast; ring
  have h2 : -((2 * Real.pi * k.val / 14 : ℝ) : ℂ) * Complex.I
      = ((-(k.val : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 14) := by push_cast; ring
  have h3 : eigval k = 2 * Complex.cos ((2 * Real.pi * k.val / 14 : ℝ) : ℂ) := by
    rw [eigval, Complex.ofReal_mul, Complex.ofReal_cos]
    norm_num
  rw [h3, Complex.two_cos, h1, h2, Complex.exp_int_mul, Complex.exp_int_mul, om]

lemma dftMat_apply (m k : Fin 14) : dftMat m k = om ^ ((m.val * k.val : ℕ) : ℤ) := by
  rw [zpow_natCast]
  simp [dftMat, Matrix.vandermonde, ← pow_mul]

lemma cycle14_neighborFinset (j : Fin 14) :
    (SimpleGraph.cycleGraph 14).neighborFinset j = {j - 1, j + 1} :=
  SimpleGraph.cycleGraph_neighborFinset (n := 12)

lemma fin14_pred_ne_succ (j : Fin 14) : j - 1 ≠ j + 1 := by decide +revert

/-- The adjacency matrix of `C₁₄` is diagonalized by the discrete Fourier (Vandermonde) matrix. -/
lemma adj_mul_dft :
    SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 14) * dftMat
      = dftMat * Matrix.diagonal eigval := by
  ext j k
  have hL : (SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 14) * dftMat) j k
      = ∑ m ∈ (SimpleGraph.cycleGraph 14).neighborFinset j, dftMat m k := by
    rw [show (SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 14) * dftMat) j k
        = (SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 14) *ᵥ fun m => dftMat m k) j from rfl,
      SimpleGraph.adjMatrix_mulVec_apply]
  rw [hL, cycle14_neighborFinset, Finset.sum_pair (fin14_pred_ne_succ j),
    Matrix.mul_diagonal, dftMat_apply, dftMat_apply, dftMat_apply, eigval_eq, mul_add,
    ← zpow_add₀ om_ne_zero, ← zpow_add₀ om_ne_zero]
  have e2 : om ^ ((((j - 1).val * k.val : ℕ)) : ℤ)
      = om ^ (((j.val * k.val : ℕ) : ℤ) + -(k.val : ℤ)) := by
    refine om_zpow_eq ?_
    have hq : ((j - 1).val : ℕ) = (j.val + 13) % 14 := by simp [Fin.sub_def]; omega
    have h : (14 : ℤ) ∣ (((j - 1).val : ℤ) - (j.val : ℤ) + 1) := by
      have hj := j.isLt; omega
    obtain ⟨c, hc⟩ := h
    refine ⟨c * k.val, ?_⟩
    push_cast
    nlinarith [hc]
  have e1 : om ^ ((((j + 1).val * k.val : ℕ)) : ℤ)
      = om ^ (((j.val * k.val : ℕ) : ℤ) + (k.val : ℤ)) := by
    refine om_zpow_eq ?_
    have hp : ((j + 1).val : ℕ) = (j.val + 1) % 14 := by simp [Fin.add_def]
    have h : (14 : ℤ) ∣ (((j + 1).val : ℤ) - (j.val : ℤ) - 1) := by
      have hj := j.isLt; omega
    obtain ⟨c, hc⟩ := h
    refine ⟨c * k.val, ?_⟩
    push_cast
    nlinarith [hc]
  rw [e1, e2, add_comm]

lemma dftMat_det_ne_zero : (dftMat).det ≠ 0 := by
  rw [dftMat, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  have hij : i < j := Finset.mem_Ioi.mp hj
  refine sub_ne_zero_of_ne fun h => ?_
  have := om_prim.pow_inj j.isLt i.isLt h
  exact absurd (Fin.ext this) (ne_of_gt hij)

/-- The adjacency matrix of `C₁₄` is conjugate (by the invertible Fourier matrix) to the
diagonal matrix of the Hückel eigenvalues. -/
lemma exists_unit_conj_diagonal : ∃ u : (Matrix (Fin 14) (Fin 14) ℂ)ˣ,
    SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 14)
      = (u : Matrix (Fin 14) (Fin 14) ℂ) * Matrix.diagonal eigval
          * (↑u⁻¹ : Matrix (Fin 14) (Fin 14) ℂ) := by
  have hdet : IsUnit (dftMat).det := isUnit_iff_ne_zero.mpr dftMat_det_ne_zero
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det dftMat).mpr hdet
  refine ⟨u, ?_⟩
  rw [Matrix.coe_units_inv, hu, ← adj_mul_dft, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv dftMat hdet, Matrix.mul_one]

/-- **Hückel theory for the annulene C₁₄.**  The spectrum of the adjacency matrix of the cycle
graph `C₁₄` is exactly `{2 cos (2πk/14) : k = 0, …, 13}`. -/
theorem huckel_C14 :
    spectrum ℂ (SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 14)) =
      {z : ℂ | ∃ k : Fin 14, z = ((2 * Real.cos (2 * Real.pi * k.val / 14) : ℝ) : ℂ)} := by
  obtain ⟨u, hA⟩ := exists_unit_conj_diagonal
  rw [hA, spectrum.units_conjugate, spectrum_diagonal]
  ext z
  simp only [Set.mem_range, Set.mem_setOf_eq, eigval, eq_comm]

/-- The characteristic polynomial of the adjacency matrix of `C₁₄` splits as
`∏_{k=0}^{13} (X - 2 cos (2πk/14))`; this records the eigenvalues with multiplicity. -/
theorem huckel_C14_charpoly :
    (SimpleGraph.adjMatrix ℂ (SimpleGraph.cycleGraph 14)).charpoly =
      ∏ k : Fin 14, (Polynomial.X -
        Polynomial.C ((2 * Real.cos (2 * Real.pi * k.val / 14) : ℝ) : ℂ)) := by
  obtain ⟨u, hA⟩ := exists_unit_conj_diagonal
  rw [hA, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]
  rfl

end Chem

