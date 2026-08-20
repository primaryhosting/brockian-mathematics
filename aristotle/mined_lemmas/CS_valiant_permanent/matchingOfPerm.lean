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

def matchingOfPerm (I : Inst) (σ : {σ : Equiv.Perm (Fin I.size) // ∀ i, I.edge i (σ i)}) :
    (biGraph I).Subgraph where
  verts := Set.univ
  Adj := fun x y =>
    match x, y with
    | Sum.inl i, Sum.inr j => σ.1 i = j
    | Sum.inr j, Sum.inl i => σ.1 i = j
    | _, _ => False
  adj_sub := by
    rintro (i | i) (j | j) h <;> simp_all [biGraph, biAdj]
    · exact h ▸ σ.2 i
    · exact h ▸ σ.2 j
  edge_vert := by intros; trivial
  symm := by rintro (i | i) (j | j) h <;> simp_all

