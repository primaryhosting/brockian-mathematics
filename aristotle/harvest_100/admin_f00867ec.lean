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

open Matrix Polynomial SimpleGraph

namespace Chem

/-- The adjacency matrix of the cycle graph `C₆` (the Hückel matrix of benzene,
with `α = 0`, `β = 1`). -/
noncomputable def C6 : Matrix (Fin 6) (Fin 6) ℝ := (cycleGraph 6).adjMatrix ℝ

/-- Explicit form of the adjacency matrix of `C₆`. -/
lemma C6_eq :
    C6 = !![0,1,0,0,0,1;
            1,0,1,0,0,0;
            0,1,0,1,0,0;
            0,0,1,0,1,0;
            0,0,0,1,0,1;
            1,0,0,0,1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C6, SimpleGraph.adjMatrix_apply, cycleGraph_adj, Fin.ext_iff] <;> decide

/-- Matrix whose `k`-th column is a (real) eigenvector of `C6` for the eigenvalue
`2 cos (2πk/6)`. -/
noncomputable def eigenBasis : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1, 1, 1, 1, 0, 0;
     1, 1/2, -1/2, -1, 1, 1;
     1, -1/2, -1/2, 1, -1, 1;
     1, -1, 1, -1, 0, 0;
     1, -1/2, -1/2, 1, 1, -1;
     1, 1/2, -1/2, -1, -1, -1]

/-- The inverse of `eigenBasis`. -/
noncomputable def eigenBasisInv : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1/6, 1/6, 1/6, 1/6, 1/6, 1/6;
     1/3, 1/6, -1/6, -1/3, -1/6, 1/6;
     1/3, -1/6, -1/6, 1/3, -1/6, -1/6;
     1/6, -1/6, 1/6, -1/6, 1/6, -1/6;
     0, 1/4, -1/4, 0, 1/4, -1/4;
     0, 1/4, 1/4, 0, -1/4, -1/4]

/-- The list of Hückel eigenvalues, in the order `2 cos (2πk/6)`, `k = 0,…,5`. -/
noncomputable def spec : Fin 6 → ℝ := ![2, 1, -1, -2, -1, 1]

lemma spec_eq_cos (k : Fin 6) : spec k = 2 * Real.cos (2 * Real.pi * k / 6) := by
  have h3 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
  obtain ⟨n, hn⟩ := k
  interval_cases n
  · norm_num [spec]
  · rw [show (2 * Real.pi * ((⟨1, hn⟩ : Fin 6) : ℕ) / 6 : ℝ) = Real.pi / 3 by
      push_cast [Fin.val_mk]; ring]
    norm_num [spec, h3]
  · rw [show (2 * Real.pi * ((⟨2, hn⟩ : Fin 6) : ℕ) / 6 : ℝ) = Real.pi - Real.pi / 3 by
      push_cast [Fin.val_mk]; ring]
    norm_num [spec, Real.cos_pi_sub, h3]
  · rw [show (2 * Real.pi * ((⟨3, hn⟩ : Fin 6) : ℕ) / 6 : ℝ) = Real.pi by
      push_cast [Fin.val_mk]; ring]
    norm_num [spec, Real.cos_pi]
  · rw [show (2 * Real.pi * ((⟨4, hn⟩ : Fin 6) : ℕ) / 6 : ℝ) = Real.pi + Real.pi / 3 by
      push_cast [Fin.val_mk]; ring]
    norm_num [spec, Real.cos_add, Real.cos_pi, Real.sin_pi, h3]
  · rw [show (2 * Real.pi * ((⟨5, hn⟩ : Fin 6) : ℕ) / 6 : ℝ) = 2 * Real.pi - Real.pi / 3 by
      push_cast [Fin.val_mk]; ring]
    norm_num [spec, Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi, h3]

set_option maxHeartbeats 1000000 in
lemma eigenBasis_mul_inv : eigenBasis * eigenBasisInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eigenBasis, eigenBasisInv, Matrix.mul_apply, Fin.sum_univ_six] <;> norm_num

set_option maxHeartbeats 1000000 in
lemma inv_mul_eigenBasis : eigenBasisInv * eigenBasis = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eigenBasis, eigenBasisInv, Matrix.mul_apply, Fin.sum_univ_six] <;> norm_num

/-- The diagonal matrix of Hückel eigenvalues, explicitly. -/
lemma diagonal_spec_eq :
    diagonal spec = !![2,0,0,0,0,0;
                       0,1,0,0,0,0;
                       0,0,-1,0,0,0;
                       0,0,0,-2,0,0;
                       0,0,0,0,-1,0;
                       0,0,0,0,0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spec]

set_option maxHeartbeats 2000000 in
/-- `C6` is diagonalized by `eigenBasis`, with diagonal entries the Hückel eigenvalues. -/
lemma C6_conj : eigenBasis * diagonal spec * eigenBasisInv = C6 := by
  rw [C6_eq, diagonal_spec_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eigenBasis, eigenBasisInv, Matrix.mul_apply, Fin.sum_univ_six] <;> norm_num

/-- The characteristic polynomial of the adjacency matrix of `C₆` factors as
`∏ₖ (X - 2 cos (2πk/6))`. -/
lemma C6_charpoly :
    C6.charpoly = ∏ k : Fin 6, (X - C (2 * Real.cos (2 * Real.pi * k / 6))) := by
  set u : (Matrix (Fin 6) (Fin 6) ℝ)ˣ :=
    ⟨eigenBasis, eigenBasisInv, eigenBasis_mul_inv, inv_mul_eigenBasis⟩
  have hval : (↑u : Matrix (Fin 6) (Fin 6) ℝ) = eigenBasis := rfl
  have hinv : ((u⁻¹ : (Matrix (Fin 6) (Fin 6) ℝ)ˣ) : Matrix (Fin 6) (Fin 6) ℝ)
      = eigenBasisInv := rfl
  have h := Matrix.charpoly_units_conj u (diagonal spec)
  rw [hval, hinv, C6_conj] at h
  rw [h, Matrix.charpoly_diagonal]
  exact Finset.prod_congr rfl fun k _ => by rw [spec_eq_cos k]

/-- **Hückel theory for benzene (C₆).** The eigenvalues of the adjacency matrix of the
cycle graph `C₆` are exactly the numbers `2 cos (2πk/6)`, `k = 0, …, 5`; moreover the
characteristic polynomial factors as `∏ₖ (X - 2 cos (2πk/6))`, so these are the
eigenvalues with multiplicity. -/
theorem huckel_C6 :
    ((cycleGraph 6).adjMatrix ℝ).charpoly =
        ∏ k : Fin 6, (X - C (2 * Real.cos (2 * Real.pi * k / 6))) ∧
      ∀ μ : ℝ,
        (∃ v : Fin 6 → ℝ, v ≠ 0 ∧ ((cycleGraph 6).adjMatrix ℝ) *ᵥ v = μ • v) ↔
          ∃ k : Fin 6, μ = 2 * Real.cos (2 * Real.pi * k / 6) := by
  refine ⟨C6_charpoly, fun μ => ?_⟩
  have hscalar : (Matrix.scalar (Fin 6)) μ = μ • (1 : Matrix (Fin 6) (Fin 6) ℝ) := by
    simp [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  have key : ∀ v : Fin 6 → ℝ,
      (((cycleGraph 6).adjMatrix ℝ) *ᵥ v = μ • v) ↔
        ((Matrix.scalar (Fin 6)) μ - (cycleGraph 6).adjMatrix ℝ) *ᵥ v = 0 := by
    intro v
    rw [sub_mulVec, sub_eq_zero, hscalar, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact eq_comm
  constructor
  · rintro ⟨v, hv, hAv⟩
    have hdet : ((Matrix.scalar (Fin 6)) μ - (cycleGraph 6).adjMatrix ℝ).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv, (key v).1 hAv⟩
    have heval : (C6.charpoly).eval μ = 0 := by
      rw [Matrix.eval_charpoly]; exact hdet
    rw [C6_charpoly] at heval
    simp only [eval_prod, eval_sub, eval_X, eval_C] at heval
    obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 heval
    exact ⟨k, by linarith [sub_eq_zero.1 hk]⟩
  · rintro ⟨k, hk⟩
    have heval : (C6.charpoly).eval μ = 0 := by
      rw [C6_charpoly]
      simp only [eval_prod, eval_sub, eval_X, eval_C]
      exact Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk]; ring)
    rw [Matrix.eval_charpoly] at heval
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 heval
    exact ⟨v, hv, (key v).2 hv0⟩

end Chem

