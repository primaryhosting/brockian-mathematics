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

def Valid (A : Matrix (Fin n) (Fin n) ℕ) (τ : Perm (Vtx n K)) : Prop :=
  ∀ x, gadget A K (τ x) x = 1

instance (A : Matrix (Fin n) (Fin n) ℕ) (τ : Perm (Vtx n K)) : Decidable (Valid A τ) := by
  unfold Valid; infer_instance

/-- A valid permutation sends an original vertex to the midpoint prescribed by
`rowFun` and `colFun`, which is moreover live. -/
