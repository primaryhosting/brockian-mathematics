import Mathlib
/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Matrix

namespace Chem

/-- The Hückel (adjacency) matrix of the cycle `C₄`: `A i j = 1` exactly when the carbon
atoms `i` and `j` are neighbours in the four-membered ring. -/
noncomputable def C4 : Matrix (Fin 4) (Fin 4) ℝ :=
  (SimpleGraph.cycleGraph 4).adjMatrix ℝ

lemma C4_eq : C4 = !![0, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C4] <;> decide

lemma det_smul_one_sub_C4 (mu : ℝ) :
    (mu • (1 : Matrix (Fin 4) (Fin 4) ℝ) - C4).det = mu ^ 4 - 4 * mu ^ 2 := by
  have h : mu • (1 : Matrix (Fin 4) (Fin 4) ℝ) - C4 =
      !![mu, -1, 0, -1; -1, mu, -1, 0; 0, -1, mu, -1; -1, 0, -1, mu] := by
    rw [C4_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [h]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove]
  ring

lemma quartic_root_iff (mu : ℝ) :
    mu ^ 4 - 4 * mu ^ 2 = 0 ↔ mu = 2 ∨ mu = 0 ∨ mu = -2 := by
  constructor
  · intro h
    have h2 : mu ^ 2 * ((mu - 2) * (mu + 2)) = 0 := by nlinarith [h]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact Or.inr (Or.inl (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3))
    · rcases mul_eq_zero.mp h3 with h4 | h4
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inr (by linarith))
  · rintro (rfl | rfl | rfl) <;> norm_num

lemma huckel_cos_zero : 2 * Real.cos (2 * Real.pi * (0 : ℕ) / 4) = 2 := by
  norm_num

lemma huckel_cos_one : 2 * Real.cos (2 * Real.pi * (1 : ℕ) / 4) = 0 := by
  rw [show (2 * Real.pi * (1 : ℕ) / 4 : ℝ) = Real.pi / 2 by push_cast; ring,
    Real.cos_pi_div_two, mul_zero]

lemma huckel_cos_two : 2 * Real.cos (2 * Real.pi * (2 : ℕ) / 4) = -2 := by
  rw [show (2 * Real.pi * (2 : ℕ) / 4 : ℝ) = Real.pi by push_cast; ring, Real.cos_pi]
  norm_num

lemma huckel_cos_three : 2 * Real.cos (2 * Real.pi * (3 : ℕ) / 4) = 0 := by
  rw [show (2 * Real.pi * (3 : ℕ) / 4 : ℝ) = Real.pi / 2 + Real.pi by push_cast; ring,
    Real.cos_add_pi, Real.cos_pi_div_two, neg_zero, mul_zero]

/-- The eigenvalues (spectrum) of the adjacency matrix of the cycle graph `C₄` are exactly the
Hückel values `2 cos (2πk/4)` for `k = 0, 1, 2, 3`, i.e. `2, 0, 0, -2`. -/
theorem huckel_C4 (mu : ℝ) :
    mu ∈ spectrum ℝ C4 ↔ ∃ k : Fin 4, mu = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 4) := by
  have hspec : mu ∈ spectrum ℝ C4 ↔ (mu • (1 : Matrix (Fin 4) (Fin 4) ℝ) - C4).det = 0 := by
    rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero, not_not]
  rw [hspec, det_smul_one_sub_C4, quartic_root_iff]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, huckel_cos_zero.symm⟩
    · exact ⟨1, huckel_cos_one.symm⟩
    · exact ⟨2, huckel_cos_two.symm⟩
  · rintro ⟨⟨v, hv⟩, rfl⟩
    interval_cases v
    · exact Or.inl huckel_cos_zero
    · exact Or.inr (Or.inl huckel_cos_one)
    · exact Or.inr (Or.inr huckel_cos_two)
    · exact Or.inr (Or.inl huckel_cos_three)

/-- Explicit Hückel molecular orbitals of `C₄`: for each `k` there is a nonzero eigenvector
of the adjacency matrix with eigenvalue `2 cos (2πk/4)`. -/
theorem huckel_C4_eigenvector (k : Fin 4) :
    ∃ v : Fin 4 → ℝ, v ≠ 0 ∧
      C4.mulVec v = (2 * Real.cos (2 * Real.pi * (k : ℕ) / 4)) • v := by
  rcases k with ⟨v, hv⟩
  interval_cases v
  · refine ⟨![1, 1, 1, 1], ?_, ?_⟩
    · intro h
      have := congrFun h 0
      norm_num at this
    · rw [huckel_cos_zero, C4_eq]
      ext i
      fin_cases i <;> norm_num [Matrix.mulVec, Fin.sum_univ_four]
  · refine ⟨![1, 0, -1, 0], ?_, ?_⟩
    · intro h
      have := congrFun h 0
      norm_num at this
    · rw [huckel_cos_one, C4_eq]
      ext i
      fin_cases i <;> norm_num [Matrix.mulVec, Fin.sum_univ_four]
  · refine ⟨![1, -1, 1, -1], ?_, ?_⟩
    · intro h
      have := congrFun h 0
      norm_num at this
    · rw [huckel_cos_two, C4_eq]
      ext i
      fin_cases i <;> norm_num [Matrix.mulVec, Fin.sum_univ_four]
  · refine ⟨![0, 1, 0, -1], ?_, ?_⟩
    · intro h
      have := congrFun h 1
      norm_num at this
    · rw [huckel_cos_three, C4_eq]
      ext i
      fin_cases i <;> norm_num [Matrix.mulVec, Fin.sum_univ_four]

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

