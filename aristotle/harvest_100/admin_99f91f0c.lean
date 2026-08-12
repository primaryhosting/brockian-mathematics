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
def A6 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0,1,0,0,0,1;
     1,0,1,0,0,0;
     0,1,0,1,0,0;
     0,0,1,0,1,0;
     0,0,0,1,0,1;
     1,0,0,0,1,0]

/-- The square of the adjacency matrix of `C₆`, written out explicitly. -/
def B6 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![2,0,1,0,1,0;
     0,2,0,1,0,1;
     1,0,2,0,1,0;
     0,1,0,2,0,1;
     1,0,1,0,2,0;
     0,1,0,1,0,2]

/-- The adjacency matrix of Mathlib's `cycleGraph 6` is `A6`. -/
lemma adjMatrix_cycleGraph_six : (SimpleGraph.cycleGraph 6).adjMatrix ℝ = A6 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A6, SimpleGraph.adjMatrix_apply, SimpleGraph.cycleGraph_adj, Fin.ext_iff] <;> decide

lemma A6_mul_A6 : A6 * A6 = B6 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A6, B6, Matrix.mul_apply, Fin.sum_univ_six] <;> norm_num

lemma B6_mul_B6 : B6 * B6 = (5 : ℝ) • B6 - (4 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B6, Matrix.mul_apply, Fin.sum_univ_six, Matrix.smul_apply, Matrix.sub_apply] <;>
      norm_num

/-- Every eigenvalue of the adjacency matrix of `C₆` is a root of `X⁴ - 5X² + 4`. -/
lemma eigenvalue_quartic {μ : ℝ} {v : Fin 6 → ℝ} (hv : v ≠ 0) (h : A6 *ᵥ v = μ • v) :
    μ ^ 4 - 5 * μ ^ 2 + 4 = 0 := by
  have hB : B6 *ᵥ v = (μ ^ 2) • v := by
    rw [← A6_mul_A6, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, h, smul_smul]
    ring_nf
  have hBB : (B6 * B6) *ᵥ v = (μ ^ 4) • v := by
    rw [← Matrix.mulVec_mulVec, hB, Matrix.mulVec_smul, hB, smul_smul]
    ring_nf
  rw [B6_mul_B6] at hBB
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, hB, Matrix.one_mulVec,
    smul_smul] at hBB
  have hzero : (μ ^ 4 - 5 * μ ^ 2 + 4) • v = 0 := by
    rw [add_smul, sub_smul, ← hBB]
    abel
  rcases smul_eq_zero.mp hzero with h' | h'
  · exact h'
  · exact absurd h' hv

/-- The values `2 cos (2πk/6)`, `k = 0,…,5`, are exactly `2, 1, -1, -2`. -/
lemma two_cos_values (μ : ℝ) :
    (∃ k ∈ Finset.range 6, μ = 2 * Real.cos (2 * Real.pi * k / 6)) ↔
      (μ = 2 ∨ μ = 1 ∨ μ = -1 ∨ μ = -2) := by
  have h1 : Real.cos (2 * Real.pi * (1 : ℕ) / 6) = 1 / 2 := by
    rw [show (2 * Real.pi * (1 : ℕ) / 6 : ℝ) = Real.pi / 3 by push_cast; ring]
    exact Real.cos_pi_div_three
  have h2 : Real.cos (2 * Real.pi * (2 : ℕ) / 6) = -(1 / 2) := by
    rw [show (2 * Real.pi * (2 : ℕ) / 6 : ℝ) = Real.pi - Real.pi / 3 by push_cast; ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
  have h3 : Real.cos (2 * Real.pi * (3 : ℕ) / 6) = -1 := by
    rw [show (2 * Real.pi * (3 : ℕ) / 6 : ℝ) = Real.pi by push_cast; ring, Real.cos_pi]
  have h4 : Real.cos (2 * Real.pi * (4 : ℕ) / 6) = -(1 / 2) := by
    rw [show (2 * Real.pi * (4 : ℕ) / 6 : ℝ) = Real.pi / 3 + Real.pi by push_cast; ring,
      Real.cos_add_pi, Real.cos_pi_div_three]
  have h5 : Real.cos (2 * Real.pi * (5 : ℕ) / 6) = 1 / 2 := by
    rw [show (2 * Real.pi * (5 : ℕ) / 6 : ℝ) = 2 * Real.pi - Real.pi / 3 by push_cast; ring,
      Real.cos_two_pi_sub, Real.cos_pi_div_three]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [Finset.mem_range] at hk
    interval_cases k
    · norm_num
    · rw [h1]; norm_num
    · rw [h2]; norm_num
    · rw [h3]; norm_num
    · rw [h4]; norm_num
    · rw [h5]; norm_num
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, by simp, by norm_num⟩
    · exact ⟨1, by simp, by rw [h1]; norm_num⟩
    · exact ⟨2, by simp, by rw [h2]; norm_num⟩
    · exact ⟨3, by simp, by rw [h3]; norm_num⟩

/-- Explicit eigenvectors: for each of `2, 1, -1, -2` there is a nonzero eigenvector. -/
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
theorem huckel_C6 (μ : ℝ) :
    (∃ v : Fin 6 → ℝ, v ≠ 0 ∧ (SimpleGraph.cycleGraph 6).adjMatrix ℝ *ᵥ v = μ • v) ↔
      ∃ k ∈ Finset.range 6, μ = 2 * Real.cos (2 * Real.pi * k / 6) := by
  rw [adjMatrix_cycleGraph_six, two_cos_values]
  constructor
  · rintro ⟨v, hv, h⟩
    have hq := eigenvalue_quartic hv h
    have : (μ - 2) * (μ - 1) * (μ + 1) * (μ + 2) = 0 := by nlinarith [hq]
    rcases mul_eq_zero.mp this with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · rcases mul_eq_zero.mp h'' with h₃ | h₃
        · exact Or.inl (by linarith)
        · exact Or.inr (Or.inl (by linarith))
      · exact Or.inr (Or.inr (Or.inl (by linarith)))
    · exact Or.inr (Or.inr (Or.inr (by linarith)))
  · exact exists_eigenvector

end Chem

#print axioms Chem.huckel_C6

