/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Polynomial Real

/-- Adjacency matrix of the cycle graph `C n` on the vertex set `Fin n`:
vertices `i` and `j` are adjacent iff they are consecutive modulo `n`. -/
def cycleAdj (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val then 1 else 0

/-- Explicit form of the adjacency matrix of `C 4`. -/
lemma cycleAdj_four :
    cycleAdj 4 = !![(0 : ℝ), 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycleAdj]

set_option maxHeartbeats 1000000 in
/-- The characteristic polynomial of the adjacency matrix of `C 4`. -/
lemma charpoly_cycleAdj_four : (cycleAdj 4).charpoly = X ^ 4 - 4 * X ^ 2 := by
  have h : Matrix.charmatrix (cycleAdj 4)
      = !![X, -1, 0, -1; -1, X, -1, 0; 0, -1, X, -1; -1, 0, -1, X] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cycleAdj_four, Matrix.charmatrix]
  rw [Matrix.charpoly, h]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- The Hückel eigenvalues `2 cos (2πk/4)`, `k = 0,1,2,3`, are `2, 0, -2, 0`. -/
lemma prod_huckel_roots :
    (∏ k : Fin 4, (X - C (2 * Real.cos (2 * π * (k : ℕ) / 4)))) = X ^ 4 - 4 * X ^ 2 := by
  have h1 : (2 * π * (1 : ℕ) / 4 : ℝ) = π / 2 := by push_cast; ring
  have h2 : (2 * π * (2 : ℕ) / 4 : ℝ) = π := by push_cast; ring
  have h3 : (2 * π * (3 : ℕ) / 4 : ℝ) = π + π / 2 := by push_cast; ring
  rw [Fin.prod_univ_four]
  norm_num [h1, h2, h3, Real.cos_add]
  ring

/-- **Hückel theory for cyclobutadiene (C₄).**
The characteristic polynomial of the adjacency matrix of the cycle graph `C 4`
factors as `∏ k, (X - 2 cos (2πk/4))`; equivalently, the adjacency eigenvalues of
`C 4` are exactly `2 cos (2πk/4)` for `k = 0, 1, 2, 3` (counted with multiplicity). -/
theorem huckel_C4 :
    (cycleAdj 4).charpoly = ∏ k : Fin 4, (X - C (2 * Real.cos (2 * π * (k : ℕ) / 4))) := by
  rw [charpoly_cycleAdj_four, prod_huckel_roots]

/-- The eigenvalues (roots of the characteristic polynomial) of the adjacency matrix
of `C 4` are exactly the numbers `2 cos (2πk/4)`, `k = 0,1,2,3`. -/
theorem huckel_C4_roots (x : ℝ) :
    (cycleAdj 4).charpoly.IsRoot x ↔ ∃ k : Fin 4, x = 2 * Real.cos (2 * π * (k : ℕ) / 4) := by
  rw [huckel_C4]
  simp [Polynomial.IsRoot, Fin.prod_univ_four, sub_eq_zero, eq_comm, Fin.exists_fin_succ,
    Fin.prod_univ_succ]

end Chem

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

