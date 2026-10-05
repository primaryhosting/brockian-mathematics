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

def gadgetPerm (σ : Perm (Fin n)) (t : Fin n → Fin (K + 1)) : Perm (Vtx n K) where
  toFun x := match x with
    | Sum.inl c => Sum.inr (σ c, c, t c)
    | Sum.inr m => if m = (σ m.2.1, m.2.1, t m.2.1) then Sum.inl m.1 else Sum.inr m
  invFun x := match x with
    | Sum.inl r => Sum.inr (r, σ.symm r, t (σ.symm r))
    | Sum.inr m => if m = (σ m.2.1, m.2.1, t m.2.1) then Sum.inl m.2.1 else Sum.inr m
  left_inv x := by
    cases x with
    | inl c => simp
    | inr m =>
      by_cases h : m = (σ m.2.1, m.2.1, t m.2.1)
      · simp only [h, if_pos rfl]
        conv_rhs => rw [h]
        simp
      · simp [h]
  right_inv x := by
    cases x with
    | inl r => simp
    | inr m =>
      by_cases h : m = (σ m.2.1, m.2.1, t m.2.1)
      · simp only [h, if_pos rfl]
        conv_rhs => rw [h]
        simp
      · simp [h]

