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

@[simp] theorem gadgetPerm_inr (σ : Perm (Fin n)) (t : Fin n → Fin (K + 1)) (m : Mid n K) :
    gadgetPerm σ t (Sum.inr m) =
      if m = (σ m.2.1, m.2.1, t m.2.1) then Sum.inl m.1 else Sum.inr m := rfl

/-- The permutation of the original vertices read off from a permutation of the gadget graph. -/
