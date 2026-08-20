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

def biGraph (I : Inst) : SimpleGraph (Fin I.size ⊕ Fin I.size) where
  Adj := biAdj I
  symm := by rintro (i | i) (j | j) h <;> simp_all [biAdj]
  loopless := by
    constructor
    rintro (i | i) h <;> simp [biAdj] at h

/-- The number of perfect matchings of the bipartite graph attached to an instance. -/
