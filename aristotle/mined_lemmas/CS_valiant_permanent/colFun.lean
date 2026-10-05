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

def colFun (τ : Perm (Vtx n K)) (c : Fin n) : Fin (K + 1) :=
  match τ (Sum.inl c) with
  | Sum.inl _ => 0
  | Sum.inr m => m.2.2

/-- A permutation of the gadget graph contributes to the permanent iff it satisfies this
predicate. -/
