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

import Mathlib

/-!
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix

namespace Chem

/-- The adjacency matrix of the cycle graph `C₆` (the Hückel matrix of benzene with
`α = 0`, `β = 1`), written out explicitly. -/
def C6adj : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0,1,0,0,0,1; 1,0,1,0,0,0; 0,1,0,1,0,0; 0,0,1,0,1,0; 0,0,0,1,0,1; 1,0,0,0,1,0]

/-- The explicit matrix `C6adj` really is the adjacency matrix of the cycle graph on 6 vertices. -/
lemma adjMatrix_cycleGraph_six : (SimpleGraph.cycleGraph 6).adjMatrix ℂ = C6adj := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C6adj, SimpleGraph.adjMatrix_apply] <;> decide

lemma C6adj_sq :
    C6adj ^ 2 = !![2,0,1,0,1,0; 0,2,0,1,0,1; 1,0,2,0,1,0; 0,1,0,2,0,1; 1,0,1,0,2,0; 0,1,0,1,0,2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C6adj, pow_two, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

/-- The adjacency matrix of `C₆` is annihilated by `X⁴ - 5X² + 4 = (X²-1)(X²-4)`. -/
lemma C6adj_poly : C6adj ^ 4 - (5 : ℂ) • C6adj ^ 2 + (4 : ℂ) • 1 = 0 := by
  have h4 : C6adj ^ 4 = (C6adj ^ 2) ^ 2 := by rw [← pow_mul]
  rw [h4, C6adj_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_two] <;> norm_num

/-- Any eigenvalue of the adjacency matrix of `C₆` lies in `{2, 1, -1, -2}`. -/
lemma eigenvalue_mem (μ : ℂ) (v : Fin 6 → ℂ) (hv : v ≠ 0) (h : C6adj.mulVec v = μ • v) :
    μ = 2 ∨ μ = 1 ∨ μ = -1 ∨ μ = -2 := by
  have h2 : (C6adj ^ 2).mulVec v = (μ ^ 2) • v := by
    rw [pow_two, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, h, smul_smul, ← pow_two]
  have h4 : (C6adj ^ 4).mulVec v = (μ ^ 4) • v := by
    have e : C6adj ^ 4 = C6adj ^ 2 * C6adj ^ 2 := by rw [← pow_add]
    rw [e, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_smul, h2, smul_smul, ← pow_add]
  have key : (μ ^ 4 - 5 * μ ^ 2 + 4) • v = 0 := by
    have e : (C6adj ^ 4 - (5 : ℂ) • C6adj ^ 2 + (4 : ℂ) • 1).mulVec v
        = (μ ^ 4 - 5 * μ ^ 2 + 4) • v := by
      rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, h2, h4, smul_smul]
      module
    rw [← e, C6adj_poly, Matrix.zero_mulVec]
  have hscal : μ ^ 4 - 5 * μ ^ 2 + 4 = 0 := by
    rcases smul_eq_zero.1 key with h' | h'
    · exact h'
    · exact absurd h' hv
  have hfac : (μ - 2) * (μ - 1) * (μ + 1) * (μ + 2) = 0 := by linear_combination hscal
  rcases mul_eq_zero.1 hfac with h' | h'
  · rcases mul_eq_zero.1 h' with h'' | h''
    · rcases mul_eq_zero.1 h'' with h₁ | h₁
      · exact Or.inl (by linear_combination h₁)
      · exact Or.inr (Or.inl (by linear_combination h₁))
    · exact Or.inr (Or.inr (Or.inl (by linear_combination h'')))
  · exact Or.inr (Or.inr (Or.inr (by linear_combination h')))

section CosValues

lemma cos_two_pi_one_div_six : Real.cos (2 * Real.pi / 6) = 1 / 2 := by
  rw [show (2 * Real.pi / 6 : ℝ) = Real.pi / 3 by ring, Real.cos_pi_div_three]

lemma cos_two_pi_two_div_six : Real.cos (2 * Real.pi * 2 / 6) = -(1 / 2) := by
  rw [show (2 * Real.pi * 2 / 6 : ℝ) = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_three]

lemma cos_two_pi_three_div_six : Real.cos (2 * Real.pi * 3 / 6) = -1 := by
  rw [show (2 * Real.pi * 3 / 6 : ℝ) = Real.pi by ring, Real.cos_pi]

lemma cos_two_pi_four_div_six : Real.cos (2 * Real.pi * 4 / 6) = -(1 / 2) := by
  rw [show (2 * Real.pi * 4 / 6 : ℝ) = Real.pi + Real.pi / 3 by ring, Real.cos_add,
    Real.cos_pi_div_three]
  simp

lemma cos_two_pi_five_div_six : Real.cos (2 * Real.pi * 5 / 6) = 1 / 2 := by
  rw [show (2 * Real.pi * 5 / 6 : ℝ) = 2 * Real.pi - Real.pi / 3 by ring, Real.cos_sub,
    Real.cos_pi_div_three]
  simp

lemma val_zero : 2 * Real.cos (2 * Real.pi * ((0 : Fin 6) : ℕ) / 6) = 2 := by norm_num

lemma val_one : 2 * Real.cos (2 * Real.pi * ((1 : Fin 6) : ℕ) / 6) = 1 := by
  norm_num [cos_two_pi_one_div_six]

lemma val_two : 2 * Real.cos (2 * Real.pi * ((2 : Fin 6) : ℕ) / 6) = -1 := by
  norm_num [cos_two_pi_two_div_six]

lemma val_three : 2 * Real.cos (2 * Real.pi * ((3 : Fin 6) : ℕ) / 6) = -2 := by
  norm_num [cos_two_pi_three_div_six]

/-- The values `2 cos(2πk/6)`, `k = 0,…,5`, are exactly `2, 1, -1, -2, -1, 1`. -/
lemma two_cos_values (k : Fin 6) :
    2 * Real.cos (2 * Real.pi * (k : ℕ) / 6) = 2 ∨
      2 * Real.cos (2 * Real.pi * (k : ℕ) / 6) = 1 ∨
      2 * Real.cos (2 * Real.pi * (k : ℕ) / 6) = -1 ∨
      2 * Real.cos (2 * Real.pi * (k : ℕ) / 6) = -2 := by
  fin_cases k
  · exact Or.inl (by norm_num)
  · exact Or.inr (Or.inl (by norm_num [cos_two_pi_one_div_six]))
  · exact Or.inr (Or.inr (Or.inl (by norm_num [cos_two_pi_two_div_six])))
  · exact Or.inr (Or.inr (Or.inr (by norm_num [cos_two_pi_three_div_six])))
  · exact Or.inr (Or.inr (Or.inl (by norm_num [cos_two_pi_four_div_six])))
  · exact Or.inr (Or.inl (by norm_num [cos_two_pi_five_div_six]))

end CosValues

section Eigenvectors

lemma mulVec_eigen_two : C6adj.mulVec ![1,1,1,1,1,1] = (2 : ℂ) • ![1,1,1,1,1,1] := by
  ext i
  fin_cases i <;> simp [C6adj, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> norm_num

lemma mulVec_eigen_one : C6adj.mulVec ![1,1,0,-1,-1,0] = (1 : ℂ) • ![1,1,0,-1,-1,0] := by
  ext i
  fin_cases i <;> simp [C6adj, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

lemma mulVec_eigen_neg_one : C6adj.mulVec ![1,-1,0,1,-1,0] = (-1 : ℂ) • ![1,-1,0,1,-1,0] := by
  ext i
  fin_cases i <;> simp [C6adj, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

lemma mulVec_eigen_neg_two : C6adj.mulVec ![1,-1,1,-1,1,-1] = (-2 : ℂ) • ![1,-1,1,-1,1,-1] := by
  ext i
  fin_cases i <;> simp [C6adj, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> norm_num

lemma ne_zero_of_first_ne_zero (v : Fin 6 → ℂ) (h : v 0 ≠ 0) : v ≠ 0 := by
  intro hv
  exact h (by rw [hv]; rfl)

end Eigenvectors

/-- **Hückel theory for benzene (C₆).**  A complex number `μ` is an eigenvalue of the adjacency
matrix of the cycle graph `C₆` if and only if `μ = 2 cos (2πk/6)` for some `k ∈ {0,1,2,3,4,5}`.
(Equivalently, the Hückel π-orbital energies of benzene are `α + 2β cos(2πk/6)`.) -/
theorem huckel_C6 (μ : ℂ) :
    (∃ v : Fin 6 → ℂ, v ≠ 0 ∧ ((SimpleGraph.cycleGraph 6).adjMatrix ℂ).mulVec v = μ • v) ↔
      ∃ k : Fin 6, μ = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 6) : ℝ) : ℂ) := by
  rw [adjMatrix_cycleGraph_six]
  constructor
  · rintro ⟨v, hv, h⟩
    rcases eigenvalue_mem μ v hv h with h' | h' | h' | h'
    · exact ⟨0, by rw [h', val_zero]; norm_num⟩
    · exact ⟨1, by rw [h', val_one]; norm_num⟩
    · exact ⟨2, by rw [h', val_two]; norm_num⟩
    · exact ⟨3, by rw [h', val_three]; norm_num⟩
  · rintro ⟨k, hk⟩
    rcases two_cos_values k with h' | h' | h' | h'
    · refine ⟨![1,1,1,1,1,1], ne_zero_of_first_ne_zero _ (by norm_num), ?_⟩
      rw [hk, h', Complex.ofReal_ofNat]
      exact mulVec_eigen_two
    · refine ⟨![1,1,0,-1,-1,0], ne_zero_of_first_ne_zero _ (by norm_num), ?_⟩
      rw [hk, h', Complex.ofReal_one]
      exact mulVec_eigen_one
    · refine ⟨![1,-1,0,1,-1,0], ne_zero_of_first_ne_zero _ (by norm_num), ?_⟩
      rw [hk, h', Complex.ofReal_neg, Complex.ofReal_one]
      exact mulVec_eigen_neg_one
    · refine ⟨![1,-1,1,-1,1,-1], ne_zero_of_first_ne_zero _ (by norm_num), ?_⟩
      rw [hk, h', Complex.ofReal_neg, Complex.ofReal_ofNat]
      exact mulVec_eigen_neg_two

end Chem

