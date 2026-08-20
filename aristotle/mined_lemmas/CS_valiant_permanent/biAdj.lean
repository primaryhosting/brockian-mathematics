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

def biAdj (I : Inst) : Fin I.size ⊕ Fin I.size → Fin I.size ⊕ Fin I.size → Prop
  | Sum.inl i, Sum.inr j => I.edge i j
  | Sum.inr j, Sum.inl i => I.edge i j
  | _, _ => False

/-- The bipartite graph attached to an instance: left and right copies of `Fin n`,
with `inl i` adjacent to `inr j` exactly when the matrix entry `(i, j)` is `1`. -/
