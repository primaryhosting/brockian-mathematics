import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

open Finset Matrix

/-! ## Part A: the 0/1 permanent as a counting problem -/

/-- For a 0/1 matrix, the permanent counts the permutations supported on the matrix, i.e. the
perfect matchings of the associated bipartite graph (equivalently, the cycle covers of the
associated digraph). -/

theorem permanent_submatrix_equiv_self {α β R : Type} [DecidableEq α] [Fintype α] [DecidableEq β]
    [Fintype β] [CommSemiring R] (e : α ≃ β) (M : Matrix β β R) :
    (M.submatrix e e).permanent = M.permanent := by
  unfold Matrix.permanent
  refine Fintype.sum_bijective (Equiv.permCongr e) (Equiv.permCongr e).bijective _ _ ?_
  intro σ
  rw [← Equiv.prod_comp e (fun j => M ((Equiv.permCongr e σ) j) j)]
  exact Finset.prod_congr rfl fun i _ => by simp [Equiv.permCongr_apply, Matrix.submatrix_apply]

section Gadget

variable {n : ℕ}

/-- The vertices added for the weights: `A i j` parallel copies of the cell `(i, j)`. -/
abbrev Cells (A : Matrix (Fin n) (Fin n) ℕ) := (p : Fin n × Fin n) × Fin (A p.1 p.2)

/-- Vertices of the 0/1 gadget graph: the original ones plus one per cell copy. -/
abbrev Vert (A : Matrix (Fin n) (Fin n) ℕ) := Fin n ⊕ Cells A

/-- The 0/1 matrix simulating the weights of `A`: each vertex `i` points to every copy of a
cell in row `i`, every copy of a cell in column `j` points to `j`, and each cell copy carries a
self-loop. -/
