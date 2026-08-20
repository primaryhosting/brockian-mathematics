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

def matrixOf (I : Inst) : Matrix (Fin I.size) (Fin I.size) ℕ :=
  fun i j => if I.edge i j then 1 else 0

/-- The value of the 0/1 permanent problem on an instance. -/

def permanentCount (I : Inst) : ℕ := (matrixOf I).permanent

/-- The number of witnesses: permutations all of whose selected entries are `1`. -/
