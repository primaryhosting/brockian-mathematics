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

theorem exists_degree_le_three [Nonempty V] [DecidableRel G.Adj] (hp : IsPlanar G)
    (htf : G.CliqueFree 3) : ∃ v : V, G.degree v ≤ 3 := by
  by_contra hcon
  push_neg at hcon
  have hdeg : ∀ v : V, 2 ≤ Nat.card (G.neighborSet v) := fun v => by
    rw [card_neighborSet_eq_degree']
    exact le_trans (by norm_num) (hcon v)
  have hbound := planar_trianglefree_edge_bound hp htf hdeg
  have hlow := mul_card_le_two_mul_card_edgeSet 4 (fun v => hcon v)
  have hpos : (0 : ℤ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos
  push_cast at hlow
  linarith

end

section Examples

instance instIsEmptyBotDart {α : Type*} : IsEmpty ((⊥ : SimpleGraph α).Dart) := ⟨fun d => d.adj⟩

/-- The (empty) rotation system on an edgeless graph. -/
