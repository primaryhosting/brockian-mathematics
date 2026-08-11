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

open Polynomial

/-- The adjacency matrix (Hückel matrix, in units where α = 0 and β = 1) of the cycle
graph `C₃`, over the reals. -/
noncomputable def C3adj : Matrix (Fin 3) (Fin 3) ℝ :=
  (SimpleGraph.cycleGraph 3).adjMatrix ℝ

/-- Explicit form of the adjacency matrix of `C₃`. -/
theorem C3adj_eq : C3adj = !![0, 1, 1; 1, 0, 1; 1, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C3adj, SimpleGraph.adjMatrix_apply, SimpleGraph.cycleGraph_adj] <;> decide

/-- The three Hückel energies `2 cos (2πk/3)`, `k = 0, 1, 2`, are `2, -1, -1`. -/
theorem two_cos_C3 (k : Fin 3) :
    2 * Real.cos (2 * Real.pi * (k : ℕ) / 3) = if k = 0 then 2 else -1 := by
  fin_cases k <;> norm_num
  · rw [show (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]
    norm_num
  · rw [show (2 : ℝ) * Real.pi * 2 / 3 = Real.pi / 3 + Real.pi by ring, Real.cos_add_pi,
      Real.cos_pi_div_three]
    norm_num

/-- **Hückel theory for the cycle `C₃`.** A real number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₃` (i.e. there is a nonzero vector `v` with
`A v = μ v`) if and only if `μ = 2 cos (2πk/3)` for some `k ∈ {0, 1, 2}`. -/
theorem huckel_C3 (mu : ℝ) :
    (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ C3adj.mulVec v = mu • v) ↔
      ∃ k : Fin 3, mu = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 3) := by
  have hval : (∃ k : Fin 3, mu = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 3)) ↔
      (mu = 2 ∨ mu = -1) := by
    constructor
    · rintro ⟨k, rfl⟩
      rw [two_cos_C3 k]
      by_cases hk : k = 0 <;> simp [hk]
    · rintro (rfl | rfl)
      · exact ⟨0, by rw [two_cos_C3 0]; norm_num⟩
      · exact ⟨1, by rw [two_cos_C3 1]; norm_num⟩
  rw [hval]
  constructor
  · rintro ⟨v, hv, heq⟩
    have h0 := congrFun heq 0
    have h1 := congrFun heq 1
    have h2 := congrFun heq 2
    simp [C3adj_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2
    by_cases hs : v 0 + v 1 + v 2 = 0
    · right
      have hne : ∃ i, v i ≠ 0 := by
        by_contra h
        push_neg at h
        exact hv (funext fun i => h i)
      obtain ⟨i, hi⟩ := hne
      have key : ∀ x : ℝ, (mu + 1) * x = 0 → x ≠ 0 → mu = -1 := by
        intro x hx hx0
        rcases mul_eq_zero.1 hx with h | h
        · linarith
        · exact absurd h hx0
      fin_cases i
      · exact key (v 0) (by nlinarith) (by simpa using hi)
      · exact key (v 1) (by nlinarith) (by simpa using hi)
      · exact key (v 2) (by nlinarith) (by simpa using hi)
    · left
      have h : (mu - 2) * (v 0 + v 1 + v 2) = 0 := by nlinarith
      rcases mul_eq_zero.1 h with h | h
      · linarith
      · exact absurd h hs
  · rintro (rfl | rfl)
    · refine ⟨![1, 1, 1], ?_, ?_⟩
      · intro h
        have := congrFun h 0
        simp at this
      · ext i
        fin_cases i <;>
          simp [C3adj_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num
    · refine ⟨![1, -1, 0], ?_, ?_⟩
      · intro h
        have := congrFun h 0
        simp at this
      · ext i
        fin_cases i <;>
          simp [C3adj_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The characteristic polynomial of the adjacency matrix of `C₃` factors as
`∏ k, (X - 2 cos (2πk/3))`, so the eigenvalues `2 cos (2πk/3)`, `k = 0, 1, 2`, occur
with the right multiplicities. -/
theorem huckel_C3_charpoly :
    C3adj.charpoly = ∏ k : Fin 3, (X - C (2 * Real.cos (2 * Real.pi * (k : ℕ) / 3))) := by
  rw [Fin.prod_univ_three, two_cos_C3 0, two_cos_C3 1, two_cos_C3 2]
  rw [C3adj_eq, Matrix.charpoly, Matrix.charmatrix]
  simp [Matrix.det_fin_three, Polynomial.C_neg, Polynomial.C_ofNat]
  ring

end Chem

