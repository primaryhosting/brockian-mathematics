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

theorem permanent_eq_card_perms (A : Matrix V V ℕ) (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) :
    A.permanent = (univ.filter (fun σ : Perm V => ∀ i, A (σ i) i = 1)).card := by
  rw [Matrix.permanent, Finset.card_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h : ∀ i, A (σ i) i = 1
  · simp [h]
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    rw [if_neg (by simpa using ⟨i, hi⟩)]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rcases h01 (σ i) i with h0 | h1
    · exact h0
    · exact absurd h1 hi

/-- The same count, phrased over *functions* `V → V` (bit strings of length `|V| log |V|`)
subject to the polynomial-time checkable predicate "is a bijection and all selected entries
are `1`". -/
