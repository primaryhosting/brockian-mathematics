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

set_option grind.warning false

/-!
# Hückel theory for the cycle graph `C₃`

The adjacency eigenvalues of the cycle graph `C₃` (the carbon skeleton of a three-membered
conjugated ring, in Hückel theory) are exactly the numbers `2 * cos (2 * π * k / 3)` for
`k = 0, 1, 2`.

The main statement `Chem.huckel_C3` says that a real number `μ` is an eigenvalue of the
adjacency matrix of `SimpleGraph.cycleGraph 3` (i.e. there is a nonzero vector `v` with
`A *ᵥ v = μ • v`) if and only if `μ = 2 * cos (2 * π * k / 3)` for some `k : Fin 3`.

`Chem.huckel_C3_charpoly` records the stronger, multiplicity-aware version: the characteristic
polynomial of the adjacency matrix is `∏ k : Fin 3, (X - C (2 * cos (2 * π * k / 3)))`.
-/

namespace Chem

open Matrix

/-- The adjacency matrix of the cycle graph `C₃`, over `ℝ`. -/
noncomputable def adjC3 : Matrix (Fin 3) (Fin 3) ℝ :=
  (SimpleGraph.cycleGraph 3).adjMatrix ℝ

/-- Explicit form of the adjacency matrix of `C₃`. -/
theorem adjC3_eq : adjC3 = !![(0 : ℝ), 1, 1; 1, 0, 1; 1, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adjC3, SimpleGraph.adjMatrix, SimpleGraph.cycleGraph_three_eq_top]

/-- `2 * cos (2π·0/3) = 2`. -/
theorem two_cos_zero : 2 * Real.cos (2 * Real.pi * ((0 : Fin 3) : ℕ) / 3) = 2 := by
  norm_num

/-- `2 * cos (2π·1/3) = -1`. -/
theorem two_cos_one : 2 * Real.cos (2 * Real.pi * ((1 : Fin 3) : ℕ) / 3) = -1 := by
  have h : 2 * Real.pi * ((1 : Fin 3) : ℕ) / 3 = Real.pi - Real.pi / 3 := by
    norm_num; ring
  rw [h, Real.cos_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  simp

/-- `2 * cos (2π·2/3) = -1`. -/
theorem two_cos_two : 2 * Real.cos (2 * Real.pi * ((2 : Fin 3) : ℕ) / 3) = -1 := by
  have h : 2 * Real.pi * ((2 : Fin 3) : ℕ) / 3 = Real.pi + Real.pi / 3 := by
    norm_num; ring
  rw [h, Real.cos_add, Real.cos_pi_div_three, Real.sin_pi_div_three]
  simp

/-- The set of values `2 * cos (2π k / 3)`, `k : Fin 3`, is exactly `{2, -1}`. -/
theorem two_cos_range (μ : ℝ) :
    (∃ k : Fin 3, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 3)) ↔ (μ = 2 ∨ μ = -1) := by
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k
    · exact Or.inl two_cos_zero
    · exact Or.inr two_cos_one
    · exact Or.inr two_cos_two
  · rintro (rfl | rfl)
    · exact ⟨0, two_cos_zero.symm⟩
    · exact ⟨1, two_cos_one.symm⟩

/-- The real eigenvalues of the adjacency matrix of `C₃` are exactly `2` and `-1`. -/
theorem eigen_adjC3 (μ : ℝ) :
    (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ adjC3 *ᵥ v = μ • v) ↔ (μ = 2 ∨ μ = -1) := by
  rw [adjC3_eq]
  constructor
  · rintro ⟨v, hv, heq⟩
    have h0 := congrFun heq 0
    have h1 := congrFun heq 1
    have h2 := congrFun heq 2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2
    have hv' : ¬ (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0) := by
      rintro ⟨a, b, c⟩
      exact hv (funext fun i => by fin_cases i <;> simpa)
    by_cases hs : v 0 + v 1 + v 2 = 0
    · right
      have e0 : μ * v 0 = (-1) * v 0 := by linarith
      have e1 : μ * v 1 = (-1) * v 1 := by linarith
      have e2 : μ * v 2 = (-1) * v 2 := by linarith
      rcases (by tauto : v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0) with h | h | h
      · exact mul_right_cancel₀ h e0
      · exact mul_right_cancel₀ h e1
      · exact mul_right_cancel₀ h e2
    · left
      exact mul_right_cancel₀ hs (by linarith : μ * (v 0 + v 1 + v 2) = 2 * (v 0 + v 1 + v 2))
  · rintro (rfl | rfl)
    · refine ⟨![1, 1, 1], ?_, ?_⟩
      · intro h; have := congrFun h 0; simp at this
      · funext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num
    · refine ⟨![1, -1, 0], ?_, ?_⟩
      · intro h; have := congrFun h 0; simp at this
      · funext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- **Hückel theory for `C₃`.** A real number `μ` is an eigenvalue of the adjacency matrix of
the cycle graph `C₃` if and only if `μ = 2 * cos (2π k / 3)` for some `k ∈ {0, 1, 2}`. -/
theorem huckel_C3 (μ : ℝ) :
    (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ (SimpleGraph.cycleGraph 3).adjMatrix ℝ *ᵥ v = μ • v) ↔
      ∃ k : Fin 3, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 3) := by
  rw [two_cos_range]
  exact eigen_adjC3 μ

/-- Multiplicity-aware version: the characteristic polynomial of the adjacency matrix of `C₃`
factors as `∏ k : Fin 3, (X - C (2 * cos (2π k / 3)))`. -/
theorem huckel_C3_charpoly :
    ((SimpleGraph.cycleGraph 3).adjMatrix ℝ).charpoly =
      ∏ k : Fin 3, (Polynomial.X - Polynomial.C (2 * Real.cos (2 * Real.pi * (k : ℕ) / 3))) := by
  have hprod : (∏ k : Fin 3,
      (Polynomial.X - Polynomial.C (2 * Real.cos (2 * Real.pi * (k : ℕ) / 3)))) =
      Polynomial.X ^ 3 - 3 * Polynomial.X - 2 := by
    rw [Fin.prod_univ_three, two_cos_zero, two_cos_one, two_cos_two]
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [hprod, show ((SimpleGraph.cycleGraph 3).adjMatrix ℝ) = !![(0 : ℝ), 1, 1; 1, 0, 1; 1, 1, 0]
    from adjC3_eq]
  simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_fin_three]
  ring

end Chem

