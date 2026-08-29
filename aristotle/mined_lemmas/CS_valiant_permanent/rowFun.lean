import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Matrix Equiv Finset

section Counting

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Counting form of the permanent (membership in `#P`).**
The permanent of a `0/1` matrix is the number of permutations `σ` all of whose entries
`A (σ i) i` equal `1`, i.e. the number of perfect matchings of the bipartite graph
described by `A`. -/

def rowFun (τ : Perm (Vtx n K)) (c : Fin n) : Fin n :=
  match τ (Sum.inl c) with
  | Sum.inl r => r
  | Sum.inr m => m.1

/-- The choice of parallel path read off from a permutation of the gadget graph. -/
