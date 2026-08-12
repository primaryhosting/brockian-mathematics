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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open Polynomial

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₄`,
i.e. of cyclobutadiene. -/
noncomputable def C4Matrix : Matrix (Fin 4) (Fin 4) ℝ :=
  SimpleGraph.adjMatrix ℝ (SimpleGraph.cycleGraph 4)

/-- The `k`-th predicted Hückel level of `C₄`: `2 cos (2πk/4)`. -/
noncomputable def C4Level (k : Fin 4) : ℝ := 2 * Real.cos (2 * Real.pi * (k : ℕ) / 4)

lemma C4Matrix_eq : C4Matrix = !![(0 : ℝ), 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C4Matrix, SimpleGraph.adjMatrix, SimpleGraph.cycleGraph_adj] <;> decide

lemma C4Matrix_charpoly : C4Matrix.charpoly = X ^ 4 - 4 * X ^ 2 := by
  rw [C4Matrix_eq]
  have h : Matrix.charmatrix (!![(0 : ℝ), 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0])
      = !![X, -1, 0, -1; -1, X, -1, 0; 0, -1, X, -1; -1, 0, -1, X] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [Matrix.charpoly, h]
  have e1 : (Fin.succAbove (1 : Fin 4) 2) = 3 := by decide
  have e2 : (Fin.succAbove (3 : Fin 4) 2) = 2 := by decide
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, e1, e2]
  ring

lemma C4Level_values :
    C4Level 0 = 2 ∧ C4Level 1 = 0 ∧ C4Level 2 = -2 ∧ C4Level 3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [C4Level] <;> norm_num
  · rw [show (2 : ℝ) * Real.pi / 4 = Real.pi / 2 by ring, Real.cos_pi_div_two]
  · rw [show (2 : ℝ) * Real.pi * 2 / 4 = Real.pi by ring, Real.cos_pi]
    norm_num
  · rw [show (2 : ℝ) * Real.pi * 3 / 4 = Real.pi + Real.pi / 2 by ring,
      Real.cos_add, Real.cos_pi_div_two, Real.sin_pi]
    ring

/-- **Hückel theory for cyclobutadiene (`C₄`).**  The characteristic polynomial of the
adjacency matrix of the cycle graph `C₄` factors as `∏ k, (X - 2 cos (2πk/4))`; equivalently,
the adjacency eigenvalues of `C₄`, with multiplicity, are `2 cos (2πk/4)` for `k = 0, 1, 2, 3`. -/
theorem huckel_C4 :
    C4Matrix.charpoly = ∏ k : Fin 4, (X - C (C4Level k)) := by
  obtain ⟨h0, h1, h2, h3⟩ := C4Level_values
  rw [C4Matrix_charpoly, Fin.prod_univ_four, h0, h1, h2, h3]
  simp only [map_ofNat, map_zero, map_neg, sub_zero]
  ring

/-- The eigenvalues of the adjacency matrix of `C₄` are exactly the numbers
`2 cos (2πk/4)`, `k = 0, 1, 2, 3`. -/
theorem huckel_C4_eigenvalues (mu : ℝ) :
    (∃ v : Fin 4 → ℝ, v ≠ 0 ∧ C4Matrix.mulVec v = mu • v) ↔ ∃ k : Fin 4, mu = C4Level k := by
  have hroot : C4Matrix.charpoly.IsRoot mu ↔ ∃ k : Fin 4, mu = C4Level k := by
    obtain ⟨h0, h1, h2, h3⟩ := C4Level_values
    rw [C4Matrix_charpoly]
    have hev : ∀ x : ℝ, (X ^ 4 - 4 * X ^ 2 : Polynomial ℝ).IsRoot x ↔ x ^ 4 - 4 * x ^ 2 = 0 := by
      intro x; simp [Polynomial.IsRoot]
    rw [hev]
    constructor
    · intro h
      have h' : mu ^ 2 * ((mu - 2) * (mu + 2)) = 0 := by linear_combination h
      rcases mul_eq_zero.1 h' with h'' | h''
      · exact ⟨1, by rw [h1]; exact pow_eq_zero_iff two_ne_zero |>.1 h''⟩
      · rcases mul_eq_zero.1 h'' with h' | h'
        · exact ⟨0, by rw [h0]; linarith⟩
        · exact ⟨2, by rw [h2]; linarith⟩
    · rintro ⟨k, rfl⟩
      fin_cases k
      · rw [show C4Level ⟨0, by norm_num⟩ = C4Level 0 from rfl, h0]; norm_num
      · rw [show C4Level ⟨1, by norm_num⟩ = C4Level 1 from rfl, h1]; norm_num
      · rw [show C4Level ⟨2, by norm_num⟩ = C4Level 2 from rfl, h2]; norm_num
      · rw [show C4Level ⟨3, by norm_num⟩ = C4Level 3 from rfl, h3]; norm_num
  rw [← hroot]
  constructor
  · rintro ⟨v, hv, hvm⟩
    have : Module.End.HasEigenvector C4Matrix.mulVecLin mu v := by
      refine ⟨?_, hv⟩
      simp only [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply, hvm]
    have hev : Module.End.HasEigenvalue C4Matrix.mulVecLin mu :=
      Module.End.hasEigenvalue_of_hasEigenvector this
    have := (Module.End.hasEigenvalue_iff_isRoot_charpoly C4Matrix.mulVecLin mu).1 hev
    rwa [Matrix.charpoly_mulVecLin] at this
  · intro h
    have hev : Module.End.HasEigenvalue C4Matrix.mulVecLin mu := by
      refine (Module.End.hasEigenvalue_iff_isRoot_charpoly C4Matrix.mulVecLin mu).2 ?_
      rwa [Matrix.charpoly_mulVecLin]
    obtain ⟨v, hv1, hv2⟩ := hev.exists_hasEigenvector
    exact ⟨v, hv2, by
      have := (Module.End.mem_eigenspace_iff).1 hv1
      simpa [Matrix.mulVecLin_apply] using this⟩

end Chem

