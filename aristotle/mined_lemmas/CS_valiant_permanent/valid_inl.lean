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

theorem valid_inl (A : Matrix (Fin n) (Fin n) ℕ) {τ : Perm (Vtx n K)} (hτ : Valid A τ)
    (c : Fin n) :
    τ (Sum.inl c) = Sum.inr (rowFun τ c, c, colFun τ c) ∧
      ((colFun τ c : ℕ) < A (rowFun τ c) c) := by
  have h := hτ (Sum.inl c)
  revert h
  rcases hc : τ (Sum.inl c) with r | m
  · simp
  · intro h
    simp only [gadget_inr_inl] at h
    have h' : m.2.1 = c ∧ (m.2.2 : ℕ) < A m.1 m.2.1 := by
      by_contra hcon
      rw [if_neg hcon] at h
      exact absurd h (by norm_num)
    have hrow : rowFun τ c = m.1 := by simp [rowFun, hc]
    have hcol : colFun τ c = m.2.2 := by simp [colFun, hc]
    refine ⟨?_, ?_⟩
    · rw [hc, hrow, hcol, h'.1]
    · rw [hrow, hcol]
      simpa [h'.1] using h'.2

