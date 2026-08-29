import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 4000000
set_option maxRecDepth 40000

namespace Chem

open Matrix

/-- The adjacency matrix of the cycle graph `C₅` on vertices `0,1,2,3,4`:
vertices `i` and `j` are adjacent iff `j ≡ i + 1` or `i ≡ j + 1` modulo `5`. -/

lemma det_sub_C5adj (m : ℂ) :
    (m • (1 : Matrix (Fin 5) (Fin 5) ℂ) - C5adj).det = m ^ 5 - 5 * m ^ 3 + 5 * m - 2 := by
  rw [sub_C5adj_eq]
  simp +decide [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  norm_num [Fin.succAbove, Fin.lt_def, Fin.castSucc, Fin.castAdd, Fin.castLE,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
    Matrix.head_cons]
  ring

/-! ### The relevant cosine values -/

