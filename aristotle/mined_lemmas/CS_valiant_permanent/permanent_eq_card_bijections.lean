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

theorem permanent_eq_card_bijections (A : Matrix V V ℕ) (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) :
    A.permanent =
      (univ.filter (fun f : V → V => Function.Bijective f ∧ ∀ i, A (f i) i = 1)).card := by
  rw [permanent_eq_card_perms A h01]
  refine Finset.card_bij (fun σ _ => ⇑σ) ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    exact ⟨σ.bijective, hσ⟩
  · intro σ _ τ _ h
    exact Equiv.coe_fn_injective h
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    refine ⟨Equiv.ofBijective f hf.1, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    simpa using hf.2 i

end Counting

section Gadget

variable {n K : ℕ}

/-- Auxiliary ("midpoint") vertices of the gadget graph: for each pair `(i, j)` of original
vertices there are `K + 1` midpoints, of which the first `A i j` are *live*. -/
abbrev Mid (n K : ℕ) : Type := Fin n × Fin n × Fin (K + 1)

/-- Vertices of the gadget graph: the original ones together with the midpoints. -/
abbrev Vtx (n K : ℕ) : Type := Fin n ⊕ Mid n K

/-- The `0/1` gadget matrix associated with a nonnegative integer matrix `A`:
every entry `A i j` (a weight, given in unary) is replaced by `A i j` parallel length-two
paths through fresh midpoint vertices, each unused midpoint carrying a loop. -/
