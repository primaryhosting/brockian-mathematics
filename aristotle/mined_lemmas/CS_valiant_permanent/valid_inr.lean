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

theorem valid_inr (A : Matrix (Fin n) (Fin n) ℕ) {τ : Perm (Vtx n K)} (hτ : Valid A τ)
    (d : Fin n) : τ (Sum.inr (rowFun τ d, d, colFun τ d)) = Sum.inl (rowFun τ d) := by
  have hd := (valid_inl A hτ d).1
  have hne : τ (Sum.inr (rowFun τ d, d, colFun τ d)) ≠ Sum.inr (rowFun τ d, d, colFun τ d) := by
    intro hcon
    have := τ.injective (hd.trans hcon.symm)
    exact absurd this (by simp)
  have hval := hτ (Sum.inr (rowFun τ d, d, colFun τ d))
  revert hval hne
  rcases hval2 : τ (Sum.inr (rowFun τ d, d, colFun τ d)) with r | m
  · intro hval _
    simp only [gadget_inl_inr] at hval
    have : r = rowFun τ d ∧ _ := by
      by_contra hcon
      rw [if_neg hcon] at hval
      exact absurd hval (by norm_num)
    rw [this.1]
  · intro hval hne
    simp only [gadget_inr_inr] at hval
    have : m = (rowFun τ d, d, colFun τ d) := by
      by_contra hcon
      rw [if_neg hcon] at hval
      exact absurd hval (by norm_num)
    exact absurd (by rw [this]) hne

