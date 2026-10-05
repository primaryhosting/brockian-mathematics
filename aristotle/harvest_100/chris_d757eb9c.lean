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

namespace Chem

open Polynomial Matrix

/-- The Hückel (adjacency) matrix of the cycle graph `C₆` (the benzene ring), over `ℂ`. -/
noncomputable def C6adj : Matrix (Fin 6) (Fin 6) ℂ := (SimpleGraph.cycleGraph 6).adjMatrix ℂ

/-- Explicit form of the adjacency matrix of `C₆`. -/
lemma C6adj_eq :
    C6adj = !![0,1,0,0,0,1;
               1,0,1,0,0,0;
               0,1,0,1,0,0;
               0,0,1,0,1,0;
               0,0,0,1,0,1;
               1,0,0,0,1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C6adj, SimpleGraph.adjMatrix_apply, SimpleGraph.cycleGraph_adj] <;> decide

/-- Matrix whose columns are eigenvectors of the `C₆` adjacency matrix. -/
def C6P : Matrix (Fin 6) (Fin 6) ℂ :=
  !![1, 2, 2, 1, 0, 0;
     1, 1,-1,-1, 1, 1;
     1,-1,-1, 1,-1, 1;
     1,-2, 2,-1, 0, 0;
     1,-1,-1, 1, 1,-1;
     1, 1,-1,-1,-1,-1]

/-- The inverse of `C6P`. -/
noncomputable def C6Q : Matrix (Fin 6) (Fin 6) ℂ :=
  !![1/6, 1/6, 1/6, 1/6, 1/6, 1/6;
     1/6, 1/12, -1/12, -1/6, -1/12, 1/12;
     1/6, -1/12, -1/12, 1/6, -1/12, -1/12;
     1/6, -1/6, 1/6, -1/6, 1/6, -1/6;
     0, 1/4, -1/4, 0, 1/4, -1/4;
     0, 1/4, 1/4, 0, -1/4, -1/4]

/-- The eigenvalues of `C6adj`, in the order matching the columns of `C6P`. -/
def C6eig : Fin 6 → ℂ := ![2, 1, -1, -2, -1, 1]

lemma C6P_mul_C6Q : C6P * C6Q = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C6P, C6Q, Matrix.mul_apply, Fin.sum_univ_six] <;> norm_num

lemma C6Q_mul_C6P : C6Q * C6P = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C6P, C6Q, Matrix.mul_apply, Fin.sum_univ_six] <;> norm_num

lemma C6adj_mul_C6P : C6adj * C6P = C6P * diagonal C6eig := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C6adj_eq, C6P, C6eig, Matrix.mul_apply, Fin.sum_univ_six, Matrix.diagonal] <;> norm_num

lemma C6adj_conj : C6adj = C6P * diagonal C6eig * C6Q := by
  calc C6adj = C6adj * (C6P * C6Q) := by rw [C6P_mul_C6Q, mul_one]
  _ = C6adj * C6P * C6Q := by rw [mul_assoc]
  _ = C6P * diagonal C6eig * C6Q := by rw [C6adj_mul_C6P]

lemma C6adj_charpoly : C6adj.charpoly = ∏ k : Fin 6, (X - Polynomial.C (C6eig k)) := by
  have hU : (C6P * diagonal C6eig * C6Q).charpoly = (diagonal C6eig).charpoly := by
    let U : (Matrix (Fin 6) (Fin 6) ℂ)ˣ := ⟨C6P, C6Q, C6P_mul_C6Q, C6Q_mul_C6P⟩
    have h := Matrix.charpoly_units_conj U (diagonal C6eig)
    simpa [U] using h
  rw [C6adj_conj, hU, Matrix.charpoly_diagonal]

lemma two_cos_values (k : Fin 6) :
    2 * Real.cos (2 * Real.pi * (k : ℕ) / 6) = (![2, 1, -1, -2, -1, 1] : Fin 6 → ℝ) k := by
  fin_cases k <;> norm_num
  · rw [show (2 * Real.pi / 6 : ℝ) = Real.pi / 3 by ring, Real.cos_pi_div_three]; norm_num
  · rw [show (2 * Real.pi * 2 / 6 : ℝ) = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
      Real.cos_pi_div_three]; norm_num
  · rw [show (2 * Real.pi * 3 / 6 : ℝ) = Real.pi by ring, Real.cos_pi]; norm_num
  · rw [show (2 * Real.pi * 4 / 6 : ℝ) = 2 * Real.pi - (Real.pi - Real.pi / 3) by ring,
      Real.cos_two_pi_sub, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
  · rw [show (2 * Real.pi * 5 / 6 : ℝ) = 2 * Real.pi - Real.pi / 3 by ring, Real.cos_two_pi_sub,
      Real.cos_pi_div_three]; norm_num

lemma C6eig_eq_cos (k : Fin 6) :
    C6eig k = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 6) : ℝ) : ℂ) := by
  rw [two_cos_values k]
  fin_cases k <;> norm_num [C6eig]

/-- **Hückel theory for benzene (C₆).**
The characteristic polynomial of the adjacency (Hückel) matrix of the cycle graph `C₆`
factors as `∏ k, (X - 2·cos(2πk/6))`; that is, the adjacency eigenvalues of `C₆` are exactly
`2·cos(2πk/6)` for `k = 0, …, 5`, counted with multiplicity. -/
theorem huckel_C6 :
    C6adj.charpoly =
      ∏ k : Fin 6, (X - Polynomial.C ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 6) : ℝ) : ℂ)) := by
  rw [C6adj_charpoly]
  exact Finset.prod_congr rfl fun k _ => by rw [C6eig_eq_cos k]

/-- The spectrum of the `C₆` adjacency matrix, as a set: a complex number `μ` is an eigenvalue
(i.e. admits a nonzero eigenvector) if and only if `μ = 2·cos(2πk/6)` for some `k = 0, …, 5`. -/
theorem huckel_C6_spectrum (mu : ℂ) :
    (∃ v : Fin 6 → ℂ, v ≠ 0 ∧ C6adj *ᵥ v = mu • v) ↔
      ∃ k : Fin 6, mu = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 6) : ℝ) : ℂ) := by
  have hmv : ∀ v : Fin 6 → ℂ,
      ((Matrix.scalar (Fin 6)) mu - C6adj) *ᵥ v = mu • v - C6adj *ᵥ v := by
    intro v; simp [Matrix.sub_mulVec]
  have hdet : (∃ v : Fin 6 → ℂ, v ≠ 0 ∧ C6adj *ᵥ v = mu • v) ↔
      ((Matrix.scalar (Fin 6)) mu - C6adj).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    constructor
    · rintro ⟨v, hv, hvv⟩
      exact ⟨v, hv, by rw [hmv v, hvv, sub_self]⟩
    · rintro ⟨v, hv, hvv⟩
      exact ⟨v, hv, (sub_eq_zero.mp (by rw [← hmv v, hvv])).symm⟩
  rw [hdet, ← Matrix.eval_charpoly, huckel_C6]
  simp [Polynomial.eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero, eq_comm]

end Chem

