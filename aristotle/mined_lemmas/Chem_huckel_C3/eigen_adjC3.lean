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
