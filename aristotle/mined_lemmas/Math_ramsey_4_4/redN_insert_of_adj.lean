import Mathlib

/-!
# Upper bound for the Ramsey number R(4,4)

This file develops, from scratch, the classical inductive bounds on two-colour Ramsey
numbers, culminating in `Math.ramsey_upper_4_4`: every graph on a vertex set of size at
least `18` contains a `4`-clique or an independent set of size `4`.
-/

namespace Math

open Finset

variable {V : Type*} [DecidableEq V]

open scoped Classical in
/-- The neighbours of `v` inside `s` (excluding `v` itself). -/

lemma redN_insert_of_adj (G : SimpleGraph V) {a v : V} {s : Finset V} (ha : a ∉ s) (hv : v ∈ s)
    (hadj : G.Adj v a) : redN G (insert a s) v = insert a (redN G s v) := by
  have hva : v ≠ a := fun h => ha (h ▸ hv)
  ext w
  simp only [Finset.mem_insert, mem_redN]
  constructor
  · rintro ⟨⟨hw | hw, hwv⟩, hadj'⟩
    · exact Or.inl hw
    · exact Or.inr ⟨⟨hw, hwv⟩, hadj'⟩
  · rintro (rfl | ⟨⟨hw, hwv⟩, hadj'⟩)
    · exact ⟨⟨Or.inl rfl, fun h => hva h.symm⟩, hadj⟩
    · exact ⟨⟨Or.inr hw, hwv⟩, hadj'⟩

