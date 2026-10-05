/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Matrix Real

namespace Chem

/-- The adjacency matrix of the cycle graph `C₅` (the Hückel matrix of cyclopentadienyl
with `α = 0`, `β = 1`), with vertices `0,1,2,3,4` arranged in a pentagon. -/

lemma C5adj_pow_five :
    C5adj ^ 5 = (5:ℝ) • C5adj ^ 3 - (5:ℝ) • C5adj + (2:ℝ) • (1 : Matrix (Fin 5) (Fin 5) ℝ) := by
  have h2 : C5adj ^ 2 = !![2,0,1,1,0; 0,2,0,1,1; 1,0,2,0,1; 1,1,0,2,0; 0,1,1,0,2] := by
    rw [pow_two]; ext i j
    fin_cases i <;> fin_cases j <;> norm_num [C5adj, Matrix.mul_apply, Fin.sum_univ_succ]
  have h3 : C5adj ^ 3 = !![0,3,1,1,3; 3,0,3,1,1; 1,3,0,3,1; 1,1,3,0,3; 3,1,1,3,0] := by
    rw [pow_succ, h2]; ext i j
    fin_cases i <;> fin_cases j <;> norm_num [C5adj, Matrix.mul_apply, Fin.sum_univ_succ]
  have h4 : C5adj ^ 4 = !![6,1,4,4,1; 1,6,1,4,4; 4,1,6,1,4; 4,4,1,6,1; 1,4,4,1,6] := by
    rw [pow_succ, h3]; ext i j
    fin_cases i <;> fin_cases j <;> norm_num [C5adj, Matrix.mul_apply, Fin.sum_univ_succ]
  have h5 : C5adj ^ 5 = !![2,10,5,5,10; 10,2,10,5,5; 5,10,2,10,5; 5,5,10,2,10; 10,5,5,10,2] := by
    rw [pow_succ, h4]; ext i j
    fin_cases i <;> fin_cases j <;> norm_num [C5adj, Matrix.mul_apply, Fin.sum_univ_succ]
  rw [h3, h5]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [C5adj, Matrix.one_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply]

/-- Any eigenvalue of the adjacency matrix of `C₅` is a root of `x⁵ - 5x³ + 5x - 2`. -/
