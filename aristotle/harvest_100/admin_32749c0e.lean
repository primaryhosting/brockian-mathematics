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

/-
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 2000000

namespace Chem

open Matrix

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₆`,
i.e. of the benzene carbon skeleton. -/
noncomputable def C6adj : Matrix (Fin 6) (Fin 6) ℂ :=
  (SimpleGraph.cycleGraph 6).adjMatrix ℂ

/-- Explicit form of the adjacency matrix of `C₆`. -/
theorem C6adj_eq :
    C6adj = !![0,1,0,0,0,1; 1,0,1,0,0,0; 0,1,0,1,0,0; 0,0,1,0,1,0; 0,0,0,1,0,1; 1,0,0,0,1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C6adj, SimpleGraph.adjMatrix_apply, SimpleGraph.cycleGraph_adj'] <;> decide

/-- The square of the adjacency matrix of `C₆`. -/
theorem C6adj_sq :
    C6adj ^ 2 = !![2,0,1,0,1,0; 0,2,0,1,0,1; 1,0,2,0,1,0; 0,1,0,2,0,1; 1,0,1,0,2,0; 0,1,0,1,0,2] := by
  rw [pow_two, C6adj_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_six] <;> norm_num

/-- The adjacency matrix `A` of `C₆` satisfies `A⁴ = 5A² - 4I`, i.e. it is annihilated by
`(X-2)(X-1)(X+1)(X+2)`. -/
theorem C6adj_pow_four :
    C6adj ^ 4 = (5 : ℂ) • C6adj ^ 2 - (4 : ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ) := by
  have h : C6adj ^ 4 = C6adj ^ 2 * C6adj ^ 2 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]
  rw [h, C6adj_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_six] <;> norm_num

/-- The list of eigenvalues predicted by Hückel theory, `2 cos (2πk/6)`, takes exactly the
values `2, 1, -1, -2`. -/
theorem cos_values (μ : ℂ) :
    (∃ k : Fin 6, μ = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 6) : ℝ) : ℂ)) ↔
      (μ = 2 ∨ μ = 1 ∨ μ = -1 ∨ μ = -2) := by
  have h0 : Real.cos (2 * Real.pi * ((0 : ℕ) : ℝ) / 6) = 1 := by norm_num
  have h1 : Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) / 6) = 1 / 2 := by
    rw [show 2 * Real.pi * ((1 : ℕ) : ℝ) / 6 = Real.pi / 3 by push_cast; ring,
      Real.cos_pi_div_three]
  have h2 : Real.cos (2 * Real.pi * ((2 : ℕ) : ℝ) / 6) = -(1 / 2) := by
    rw [show 2 * Real.pi * ((2 : ℕ) : ℝ) / 6 = Real.pi - Real.pi / 3 by push_cast; ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
  have h3 : Real.cos (2 * Real.pi * ((3 : ℕ) : ℝ) / 6) = -1 := by
    rw [show 2 * Real.pi * ((3 : ℕ) : ℝ) / 6 = Real.pi by push_cast; ring, Real.cos_pi]
  have h4 : Real.cos (2 * Real.pi * ((4 : ℕ) : ℝ) / 6) = -(1 / 2) := by
    rw [show 2 * Real.pi * ((4 : ℕ) : ℝ) / 6 = Real.pi + Real.pi / 3 by push_cast; ring,
      Real.cos_add, Real.cos_pi_div_three, Real.sin_pi_div_three]
    simp
  have h5 : Real.cos (2 * Real.pi * ((5 : ℕ) : ℝ) / 6) = 1 / 2 := by
    rw [show 2 * Real.pi * ((5 : ℕ) : ℝ) / 6 = 2 * Real.pi - Real.pi / 3 by push_cast; ring,
      Real.cos_two_pi_sub, Real.cos_pi_div_three]
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k <;> simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
    · rw [h0]; norm_num
    · rw [h1]; norm_num
    · rw [h2]; norm_num
    · rw [h3]; norm_num
    · rw [h4]; norm_num
    · rw [h5]; norm_num
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, by rw [show (((0 : Fin 6)) : ℕ) = 0 from rfl, h0]; norm_num⟩
    · exact ⟨1, by rw [show (((1 : Fin 6)) : ℕ) = 1 from rfl, h1]; norm_num⟩
    · exact ⟨2, by rw [show (((2 : Fin 6)) : ℕ) = 2 from rfl, h2]; norm_num⟩
    · exact ⟨3, by rw [show (((3 : Fin 6)) : ℕ) = 3 from rfl, h3]; norm_num⟩

/-- Explicit eigenvectors of the `C₆` adjacency matrix for the eigenvalues `2, 1, -1, -2`. -/
theorem C6adj_has_eigenvector (mu : ℂ) (h : mu = 2 ∨ mu = 1 ∨ mu = -1 ∨ mu = -2) :
    ∃ v : Fin 6 → ℂ, v ≠ 0 ∧ C6adj.mulVec v = mu • v := by
  rcases h with rfl | rfl | rfl | rfl
  · refine ⟨![1,1,1,1,1,1], ?_, ?_⟩
    · intro hc; have := congrFun hc 0; simp at this
    · rw [C6adj_eq]; ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;> norm_num
  · refine ⟨![1,1,0,-1,-1,0], ?_, ?_⟩
    · intro hc; have := congrFun hc 0; simp at this
    · rw [C6adj_eq]; ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six]
  · refine ⟨![1,-1,0,1,-1,0], ?_, ?_⟩
    · intro hc; have := congrFun hc 0; simp at this
    · rw [C6adj_eq]; ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six]
  · refine ⟨![1,-1,1,-1,1,-1], ?_, ?_⟩
    · intro hc; have := congrFun hc 0; simp at this
    · rw [C6adj_eq]; ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;> norm_num

/-- Any eigenvalue of the `C₆` adjacency matrix is one of `2, 1, -1, -2`. -/
theorem C6adj_eigenvalue_mem (μ : ℂ) (v : Fin 6 → ℂ) (hv : v ≠ 0)
    (h : C6adj.mulVec v = μ • v) : μ = 2 ∨ μ = 1 ∨ μ = -1 ∨ μ = -2 := by
  have hpow : ∀ n : ℕ, (C6adj ^ n).mulVec v = μ ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
          mul_comm]
  have h4 := hpow 4
  rw [C6adj_pow_four] at h4
  have h2 := hpow 2
  have hsub : ((5 : ℂ) • C6adj ^ 2 - (4 : ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ)).mulVec v
      = ((5 : ℂ) * μ ^ 2 - 4) • v := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, h2, Matrix.one_mulVec]
    rw [smul_smul, sub_smul]
  rw [hsub] at h4
  have hzero : (μ ^ 4 - ((5 : ℂ) * μ ^ 2 - 4)) • v = 0 := by
    rw [sub_smul, h4, sub_self]
  have hscal : μ ^ 4 - ((5 : ℂ) * μ ^ 2 - 4) = 0 := by
    by_contra hne
    exact hv (by simpa [smul_eq_zero, hne] using hzero)
  have hfac : (μ - 2) * (μ - 1) * (μ + 1) * (μ + 2) = 0 := by
    rw [← hscal]; ring
  rcases mul_eq_zero.1 hfac with h' | h'
  · rcases mul_eq_zero.1 h' with h'' | h''
    · rcases mul_eq_zero.1 h'' with h₁ | h₁
      · exact Or.inl (by linear_combination h₁)
      · exact Or.inr (Or.inl (by linear_combination h₁))
    · exact Or.inr (Or.inr (Or.inl (by linear_combination h'')))
  · exact Or.inr (Or.inr (Or.inr (by linear_combination h')))

/-- **Hückel theory for benzene (C₆).**  A complex number `μ` is an eigenvalue of the adjacency
matrix of the cycle graph `C₆` if and only if `μ = 2 cos (2πk/6)` for some `k ∈ {0,…,5}`. -/
theorem huckel_C6 (μ : ℂ) :
    (∃ v : Fin 6 → ℂ, v ≠ 0 ∧ C6adj.mulVec v = μ • v) ↔
      ∃ k : Fin 6, μ = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 6) : ℝ) : ℂ) := by
  rw [cos_values]
  constructor
  · rintro ⟨v, hv, h⟩
    exact C6adj_eigenvalue_mem μ v hv h
  · exact C6adj_has_eigenvector μ

end Chem

