/-
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Finset

/-- An instance of the 0/1 permanent problem: a size `n` together with an `n × n`
matrix of bits, viewed equivalently as the adjacency data of a bipartite graph. -/
structure Inst where
  size : ℕ
  edge : Fin size → Fin size → Bool

/-- The 0/1 matrix (over `ℕ`) attached to an instance. -/

theorem permanent_eq_assignmentCount (I : Inst) : permanentCount I = assignmentCount I := by
  have h1 : permanentCount I
      = ∑ σ : Equiv.Perm (Fin I.size), ∏ i, (if I.edge i (σ i) then (1 : ℕ) else 0) := by
    rw [permanentCount, ← Matrix.permanent_transpose]
    rfl
  rw [h1, assignmentCount, Fintype.card_subtype]
  simp only [Finset.prod_boole, Finset.mem_univ, forall_true_left, Finset.sum_boole]
  simp

/-! ### Witnesses correspond to perfect matchings of the bipartite graph -/

/-- The perfect matching attached to a permutation all of whose entries are edges. -/
