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

@[simp] theorem gadget_inl_inr (A : Matrix (Fin n) (Fin n) ℕ) (r : Fin n) (m : Mid n K) :
    gadget A K (Sum.inl r) (Sum.inr m) =
      if r = m.1 ∧ (m.2.2 : ℕ) < A m.1 m.2.1 then 1 else 0 := rfl

