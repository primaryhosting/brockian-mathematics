import Mathlib

/-!
# Orbits of a permutation

Minimal theory of orbits of a permutation of a finite type, as needed for face counting in a
combinatorial embedding of a graph: a permutation all of whose orbits have at least `n` elements
has at most `#α / n` orbits.
-/

namespace Frontier

variable {α : Type*}

/-- The setoid on `α` whose equivalence classes are the orbits of the permutation `f`. -/

theorem card_neighborSet_induce (s : Finset V) (v : (↑s : Set V)) :
    Nat.card ((G.induce (↑s : Set V)).neighborSet v)
      = ((s.erase v.1).filter (fun w => G.Adj v.1 w)).card := by
  have e : ((G.induce (↑s : Set V)).neighborSet v)
      ≃ {x : V // x ∈ (s.erase v.1).filter (fun w => G.Adj v.1 w)} :=
    { toFun := fun w => ⟨w.1.1, by
        have hadj : G.Adj v.1 w.1.1 := w.2
        refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, w.1.2⟩, hadj⟩
        exact (G.ne_of_adj hadj).symm⟩
      invFun := fun x => ⟨⟨x.1, (Finset.mem_erase.mp (Finset.mem_filter.mp x.2).1).2⟩, by
        exact (Finset.mem_filter.mp x.2).2⟩
      left_inv := fun w => by ext; rfl
      right_inv := fun x => by ext; rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

omit [Fintype V] in
/-- A hereditarily planar graph is `5`-degenerate. -/
