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

open scoped Real

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace Chem

/-- Adjacency matrix of the cycle graph `C₆` (the Hückel connectivity matrix of benzene):
vertex `i` is adjacent to `i ± 1 mod 6`. -/
def C6adj : Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.of fun i j => if (i.val + 1) % 6 = j.val ∨ (j.val + 1) % 6 = i.val then 1 else 0

/-- The square of the adjacency matrix of `C₆`: `2` on the diagonal and `1` at distance two. -/
def C6sq : Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.of fun i j =>
    if i.val = j.val then 2
    else if (i.val + 2) % 6 = j.val ∨ (j.val + 2) % 6 = i.val then 1 else 0

/-- `C6adj` really is the adjacency matrix of the cycle graph `C₆`. -/
lemma C6adj_eq_adjMatrix : C6adj = (SimpleGraph.cycleGraph 6).adjMatrix ℂ := by
  have hadj : ∀ i j : Fin 6,
      ((i.val + 1) % 6 = j.val ∨ (j.val + 1) % 6 = i.val) ↔ (SimpleGraph.cycleGraph 6).Adj i j := by
    decide
  ext i j
  simp only [C6adj, Matrix.of_apply, SimpleGraph.adjMatrix_apply]
  exact if_congr (hadj i j) rfl rfl

lemma C6adj_mul_self : C6adj * C6adj = C6sq := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [C6adj, C6sq, Matrix.mul_apply, Fin.sum_univ_six]

lemma C6sq_mul_self :
    C6sq * C6sq = (5 : ℂ) • C6sq - (4 : ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp only [C6sq, Matrix.mul_apply, Fin.sum_univ_six, Matrix.of_apply, Matrix.sub_apply,
        Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      norm_num

/-- If `v ≠ 0` is an eigenvector of the adjacency matrix with eigenvalue `μ`, then
`μ⁴ - 5μ² + 4 = 0`, i.e. `μ ∈ {2, 1, -1, -2}`. -/
lemma eigenvalue_poly {μ : ℂ} {v : Fin 6 → ℂ} (hv : v ≠ 0) (h : C6adj.mulVec v = μ • v) :
    (μ - 2) * (μ - 1) * (μ + 1) * (μ + 2) = 0 := by
  have h2 : C6sq.mulVec v = (μ ^ 2) • v := by
    rw [← C6adj_mul_self, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, h, smul_smul, sq]
  have h4 : (C6sq * C6sq).mulVec v = (μ ^ 4) • v := by
    rw [← Matrix.mulVec_mulVec, h2, Matrix.mulVec_smul, h2, smul_smul]
    ring_nf
  have hr : (C6sq * C6sq).mulVec v = (5 * μ ^ 2 - 4) • v := by
    rw [C6sq_mul_self, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, h2, smul_smul, sub_smul]
  have hz : (μ ^ 4 - (5 * μ ^ 2 - 4)) • v = 0 := by
    rw [sub_smul, ← h4, hr, sub_self]
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  have hzi := congrFun hz i
  simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_eq_zero] at hzi
  rcases hzi with hc | hc
  · linear_combination hc
  · exact absurd hc (by simpa using hi)

lemma hasEigenvalue_of_eigenvector {μ : ℂ} {v : Fin 6 → ℂ} (hv : v ≠ 0)
    (h : C6adj.mulVec v = μ • v) : Module.End.HasEigenvalue (Matrix.toLin' C6adj) μ := by
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨?_, hv⟩
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, h]

/-- Eigenvector for the eigenvalue `2`. -/
def vTwo : Fin 6 → ℂ := ![1, 1, 1, 1, 1, 1]

/-- Eigenvector for the eigenvalue `1`. -/
def vOne : Fin 6 → ℂ := ![1, 1, 0, -1, -1, 0]

/-- Eigenvector for the eigenvalue `-1`. -/
def vNegOne : Fin 6 → ℂ := ![1, -1, 0, 1, -1, 0]

/-- Eigenvector for the eigenvalue `-2`. -/
def vNegTwo : Fin 6 → ℂ := ![1, -1, 1, -1, 1, -1]

lemma mulVec_vTwo : C6adj.mulVec vTwo = (2 : ℂ) • vTwo := by
  ext i
  fin_cases i <;>
    · simp only [C6adj, vTwo, Matrix.mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_six,
        Pi.smul_apply, smul_eq_mul, Matrix.cons_val]
      norm_num

lemma mulVec_vOne : C6adj.mulVec vOne = (1 : ℂ) • vOne := by
  ext i
  fin_cases i <;>
    · simp only [C6adj, vOne, Matrix.mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_six,
        Pi.smul_apply, smul_eq_mul, Matrix.cons_val]
      norm_num

lemma mulVec_vNegOne : C6adj.mulVec vNegOne = (-1 : ℂ) • vNegOne := by
  ext i
  fin_cases i <;>
    · simp only [C6adj, vNegOne, Matrix.mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_six,
        Pi.smul_apply, smul_eq_mul, Matrix.cons_val]
      norm_num

lemma mulVec_vNegTwo : C6adj.mulVec vNegTwo = (-2 : ℂ) • vNegTwo := by
  ext i
  fin_cases i <;>
    · simp only [C6adj, vNegTwo, Matrix.mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_six,
        Pi.smul_apply, smul_eq_mul, Matrix.cons_val]
      norm_num

lemma vTwo_ne_zero : vTwo ≠ 0 := by
  intro hc
  have := congrFun hc 0
  simp [vTwo] at this

lemma vOne_ne_zero : vOne ≠ 0 := by
  intro hc
  have := congrFun hc 0
  simp [vOne] at this

lemma vNegOne_ne_zero : vNegOne ≠ 0 := by
  intro hc
  have := congrFun hc 0
  simp [vNegOne] at this

lemma vNegTwo_ne_zero : vNegTwo ≠ 0 := by
  intro hc
  have := congrFun hc 0
  simp [vNegTwo] at this

lemma spectrum_C6adj :
    {μ : ℂ | Module.End.HasEigenvalue (Matrix.toLin' C6adj) μ} = {2, 1, -1, -2} := by
  ext μ
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    have hvec : C6adj.mulVec v = μ • v := by
      have h' := hv.apply_eq_smul
      rwa [Matrix.toLin'_apply] at h'
    have hpoly := eigenvalue_poly hv.2 hvec
    rcases mul_eq_zero.1 hpoly with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · rcases mul_eq_zero.1 h2 with h3 | h3
        · exact Or.inl (sub_eq_zero.1 h3)
        · exact Or.inr (Or.inl (sub_eq_zero.1 h3))
      · exact Or.inr (Or.inr (Or.inl (by linear_combination h2)))
    · exact Or.inr (Or.inr (Or.inr (by linear_combination h1)))
  · rintro (rfl | rfl | rfl | rfl)
    · exact hasEigenvalue_of_eigenvector vTwo_ne_zero mulVec_vTwo
    · exact hasEigenvalue_of_eigenvector vOne_ne_zero mulVec_vOne
    · exact hasEigenvalue_of_eigenvector vNegOne_ne_zero mulVec_vNegOne
    · exact hasEigenvalue_of_eigenvector vNegTwo_ne_zero mulVec_vNegTwo

/-- `2 cos (2πk/6)` as a real number, cast into `ℂ`. -/
lemma two_mul_cos_ofNat (k : ℕ) :
    2 * Complex.cos (2 * (Real.pi : ℂ) * (k : ℂ) / 6)
      = ((2 * Real.cos (2 * Real.pi * k / 6) : ℝ) : ℂ) := by
  have h : (2 * (Real.pi : ℂ) * (k : ℂ) / 6) = ((2 * Real.pi * k / 6 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h, ← Complex.ofReal_cos]
  push_cast
  ring

lemma cos_val_zero : 2 * Complex.cos (2 * (Real.pi : ℂ) * ((0 : ℕ) : ℂ) / 6) = 2 := by
  rw [two_mul_cos_ofNat, show (2 * Real.pi * ((0 : ℕ) : ℝ) / 6 : ℝ) = 0 by push_cast; ring,
    Real.cos_zero]
  norm_num

lemma cos_val_one : 2 * Complex.cos (2 * (Real.pi : ℂ) * ((1 : ℕ) : ℂ) / 6) = 1 := by
  rw [two_mul_cos_ofNat,
    show (2 * Real.pi * ((1 : ℕ) : ℝ) / 6 : ℝ) = Real.pi / 3 by push_cast; ring,
    Real.cos_pi_div_three]
  norm_num

lemma cos_val_two : 2 * Complex.cos (2 * (Real.pi : ℂ) * ((2 : ℕ) : ℂ) / 6) = -1 := by
  rw [two_mul_cos_ofNat,
    show (2 * Real.pi * ((2 : ℕ) : ℝ) / 6 : ℝ) = Real.pi - Real.pi / 3 by push_cast; ring,
    Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

lemma cos_val_three : 2 * Complex.cos (2 * (Real.pi : ℂ) * ((3 : ℕ) : ℂ) / 6) = -2 := by
  rw [two_mul_cos_ofNat, show (2 * Real.pi * ((3 : ℕ) : ℝ) / 6 : ℝ) = Real.pi by push_cast; ring,
    Real.cos_pi]
  norm_num

lemma cos_val_four : 2 * Complex.cos (2 * (Real.pi : ℂ) * ((4 : ℕ) : ℂ) / 6) = -1 := by
  rw [two_mul_cos_ofNat,
    show (2 * Real.pi * ((4 : ℕ) : ℝ) / 6 : ℝ) = 2 * Real.pi - (Real.pi - Real.pi / 3) by
      push_cast; ring,
    Real.cos_two_pi_sub, Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

lemma cos_val_five : 2 * Complex.cos (2 * (Real.pi : ℂ) * ((5 : ℕ) : ℂ) / 6) = 1 := by
  rw [two_mul_cos_ofNat,
    show (2 * Real.pi * ((5 : ℕ) : ℝ) / 6 : ℝ) = 2 * Real.pi - Real.pi / 3 by push_cast; ring,
    Real.cos_two_pi_sub, Real.cos_pi_div_three]
  norm_num

lemma cos_values :
    {μ : ℂ | ∃ k : Fin 6, μ = 2 * Complex.cos (2 * (Real.pi : ℂ) * (k : ℕ) / 6)} =
      {2, 1, -1, -2} := by
  ext μ
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k
    · exact Or.inl cos_val_zero
    · exact Or.inr (Or.inl cos_val_one)
    · exact Or.inr (Or.inr (Or.inl cos_val_two))
    · exact Or.inr (Or.inr (Or.inr cos_val_three))
    · exact Or.inr (Or.inr (Or.inl cos_val_four))
    · exact Or.inr (Or.inl cos_val_five)
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, cos_val_zero.symm⟩
    · exact ⟨1, cos_val_one.symm⟩
    · exact ⟨2, cos_val_two.symm⟩
    · exact ⟨3, cos_val_three.symm⟩

/-- **Hückel theory for benzene (C₆).** The eigenvalues of the adjacency matrix of the cycle
graph `C₆` are exactly the numbers `2 cos (2πk/6)` for `k = 0, …, 5`. -/
theorem huckel_C6 :
    {μ : ℂ | Module.End.HasEigenvalue (Matrix.toLin' ((SimpleGraph.cycleGraph 6).adjMatrix ℂ)) μ} =
      {μ : ℂ | ∃ k : Fin 6, μ = 2 * Complex.cos (2 * (Real.pi : ℂ) * (k : ℕ) / 6)} := by
  rw [← C6adj_eq_adjMatrix, spectrum_C6adj, cos_values]

end Chem

