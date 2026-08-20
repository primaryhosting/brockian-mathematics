/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Chem

/-- The adjacency matrix of the cycle graph `C₅` (the Hückel matrix of cyclopentadienyl
in units where the Coulomb integral `α = 0` and the resonance integral `β = 1`). -/
def C5adj : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, 1, 0, 0, 1;
     1, 0, 1, 0, 0;
     0, 1, 0, 1, 0;
     0, 0, 1, 0, 1;
     1, 0, 0, 1, 0]

/-- `μ • I - A` for the `C₅` adjacency matrix, written out explicitly. -/
lemma algebraMap_sub_C5adj (m : ℝ) :
    (algebraMap ℝ (Matrix (Fin 5) (Fin 5) ℝ) m - C5adj) =
      !![m, -1, 0, 0, -1;
        -1, m, -1, 0, 0;
         0, -1, m, -1, 0;
         0, 0, -1, m, -1;
        -1, 0, 0, -1, m] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C5adj, Matrix.algebraMap_matrix_apply]

/-- The characteristic polynomial of the `C₅` adjacency matrix:
`det (μ I - A) = μ⁵ - 5μ³ + 5μ - 2`. -/
lemma det_algebraMap_sub_C5adj (m : ℝ) :
    (algebraMap ℝ (Matrix (Fin 5) (Fin 5) ℝ) m - C5adj).det = m ^ 5 - 5 * m ^ 3 + 5 * m - 2 := by
  rw [algebraMap_sub_C5adj]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  norm_num [Fin.succAbove, Fin.lt_def]
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Fin.castSucc,
    Fin.castAdd, Fin.castLE, Matrix.tail_cons, Matrix.head_cons]
  ring

/-- Membership in the spectrum is exactly vanishing of the characteristic polynomial. -/
lemma mem_spectrum_C5adj_iff (m : ℝ) :
    m ∈ spectrum ℝ C5adj ↔ m ^ 5 - 5 * m ^ 3 + 5 * m - 2 = 0 := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, det_algebraMap_sub_C5adj,
    isUnit_iff_ne_zero, not_ne_iff]

lemma cos_two_pi_div_five : Real.cos (2 * π / 5) = (Real.sqrt 5 - 1) / 4 := by
  have h : (2 * π / 5) = 2 * (π / 5) := by ring
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [h, Real.cos_two_mul, Real.cos_pi_div_five]
  nlinarith [h5]

lemma cos_four_pi_div_five : Real.cos (4 * π / 5) = -(1 + Real.sqrt 5) / 4 := by
  have h : (4 * π / 5) = π - π / 5 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_five]
  ring

lemma cos_six_pi_div_five : Real.cos (6 * π / 5) = -(1 + Real.sqrt 5) / 4 := by
  have h : (6 * π / 5) = 2 * π - 4 * π / 5 := by ring
  rw [h, Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi, cos_four_pi_div_five]
  ring

lemma cos_eight_pi_div_five : Real.cos (8 * π / 5) = (Real.sqrt 5 - 1) / 4 := by
  have h : (8 * π / 5) = 2 * π - 2 * π / 5 := by ring
  rw [h, Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi, cos_two_pi_div_five]
  ring

/-- **Hückel theory for cyclopentadienyl / the cycle graph `C₅`.**
The spectrum of the adjacency matrix of `C₅` is exactly
`{2 cos (2πk/5) : k = 0, 1, 2, 3, 4}`. -/
theorem huckel_C5 :
    spectrum ℝ C5adj = Set.range (fun k : Fin 5 => 2 * Real.cos (2 * π * (k : ℕ) / 5)) := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5nn : (0:ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  ext m
  rw [mem_spectrum_C5adj_iff]
  constructor
  · intro h
    have hfac : (m - 2) * (m ^ 2 + m - 1) ^ 2 = 0 := by linear_combination h
    rcases mul_eq_zero.mp hfac with h1 | h2
    · refine ⟨0, ?_⟩
      have : m = 2 := by linarith
      simp [this]
    · have hq : m ^ 2 + m - 1 = 0 := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
        exact this
      have : (2 * m + 1 - Real.sqrt 5) * (2 * m + 1 + Real.sqrt 5) = 0 := by
        nlinarith [hq, h5]
      rcases mul_eq_zero.mp this with hA | hB
      · refine ⟨1, ?_⟩
        have hm : m = (Real.sqrt 5 - 1) / 2 := by linarith
        simp only [Fin.isValue, Fin.val_one, Nat.cast_one, mul_one]
        rw [cos_two_pi_div_five, hm]
        ring
      · refine ⟨2, ?_⟩
        have hm : m = -(1 + Real.sqrt 5) / 2 := by linarith
        have h4 : 2 * π * ((2 : Fin 5) : ℕ) / 5 = 4 * π / 5 := by
          norm_num
          ring
        simp only [h4]
        rw [cos_four_pi_div_five, hm]
        ring
  · rintro ⟨k, rfl⟩
    fin_cases k <;> norm_num
    · rw [cos_two_pi_div_five]
      linear_combination ((Real.sqrt 5 ^ 3 - 5 * Real.sqrt 5 ^ 2 - 5 * Real.sqrt 5 + 25) / 32) * h5
    · rw [show (2:ℝ) * π * 2 / 5 = 4 * π / 5 by ring, cos_four_pi_div_five]
      linear_combination
        ((-Real.sqrt 5 ^ 3 - 5 * Real.sqrt 5 ^ 2 + 5 * Real.sqrt 5 + 25) / 32) * h5
    · rw [show (2:ℝ) * π * 3 / 5 = 6 * π / 5 by ring, cos_six_pi_div_five]
      linear_combination
        ((-Real.sqrt 5 ^ 3 - 5 * Real.sqrt 5 ^ 2 + 5 * Real.sqrt 5 + 25) / 32) * h5
    · rw [show (2:ℝ) * π * 4 / 5 = 8 * π / 5 by ring, cos_eight_pi_div_five]
      linear_combination ((Real.sqrt 5 ^ 3 - 5 * Real.sqrt 5 ^ 2 - 5 * Real.sqrt 5 + 25) / 32) * h5

/-- Each of the five Hückel levels `2 cos (2πk/5)` really has a nonzero eigenvector
for the adjacency matrix of `C₅`. -/
theorem huckel_C5_eigenvector (k : Fin 5) :
    ∃ v : Fin 5 → ℝ, v ≠ 0 ∧
      C5adj.mulVec v = (2 * Real.cos (2 * π * (k : ℕ) / 5)) • v := by
  set m : ℝ := 2 * Real.cos (2 * π * (k : ℕ) / 5) with hm
  have hmem : m ∈ spectrum ℝ C5adj := by
    rw [huckel_C5]
    exact ⟨k, rfl⟩
  have hdet : (algebraMap ℝ (Matrix (Fin 5) (Fin 5) ℝ) m - C5adj).det = 0 := by
    rw [mem_spectrum_C5adj_iff] at hmem
    rw [det_algebraMap_sub_C5adj]
    exact hmem
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨v, hv0, ?_⟩
  have halg : (algebraMap ℝ (Matrix (Fin 5) (Fin 5) ℝ) m).mulVec v = m • v := by
    simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [Matrix.sub_mulVec, halg, sub_eq_zero] at hv
  exact hv.symm

end Chem

