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

theorem gadget_zero_or_one (A : Matrix (Fin n) (Fin n) ℕ) (r c : Vtx n K) :
    gadget A K r c = 0 ∨ gadget A K r c = 1 := by
  cases r <;> cases c <;> simp only [gadget_inl_inl, gadget_inl_inr, gadget_inr_inl,
    gadget_inr_inr] <;> first | (left; rfl) | (split <;> simp)

/-- The permutation of the gadget graph associated with a permutation `σ` of the original
vertices together with a choice `t` of a parallel path for each vertex. -/
