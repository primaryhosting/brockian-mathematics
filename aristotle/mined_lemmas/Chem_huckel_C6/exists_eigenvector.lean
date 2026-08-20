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

namespace Chem

open Matrix

/-- The adjacency matrix of the cycle graph `C₆`, written out explicitly. -/

lemma exists_eigenvector {μ : ℝ} (hμ : μ = 2 ∨ μ = 1 ∨ μ = -1 ∨ μ = -2) :
    ∃ v : Fin 6 → ℝ, v ≠ 0 ∧ A6 *ᵥ v = μ • v := by
  have key : ∀ w : Fin 6 → ℝ, w 0 ≠ 0 → w ≠ 0 := by
    intro w hw h
    exact hw (by rw [h]; rfl)
  rcases hμ with rfl | rfl | rfl | rfl
  · refine ⟨![1, 1, 1, 1, 1, 1], key _ (by norm_num), ?_⟩
    funext i
    fin_cases i <;>
      simp [A6, Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;> norm_num
  · refine ⟨![1, 1, 0, -1, -1, 0], key _ (by norm_num), ?_⟩
    funext i
    fin_cases i <;>
      simp [A6, Matrix.mulVec, dotProduct, Fin.sum_univ_six]
  · refine ⟨![1, -1, 0, 1, -1, 0], key _ (by norm_num), ?_⟩
    funext i
    fin_cases i <;>
      simp [A6, Matrix.mulVec, dotProduct, Fin.sum_univ_six]
  · refine ⟨![1, -1, 1, -1, 1, -1], key _ (by norm_num), ?_⟩
    funext i
    fin_cases i <;>
      simp [A6, Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;> norm_num

/-- **Hückel theory for benzene.**  The eigenvalues of the adjacency matrix of the cycle
graph `C₆` are exactly the numbers `2 cos (2πk/6)` for `k = 0, 1, …, 5`. -/
