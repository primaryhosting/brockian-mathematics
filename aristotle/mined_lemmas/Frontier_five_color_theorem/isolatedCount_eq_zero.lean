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

theorem isolatedCount_eq_zero (hdeg : ∀ v : V, 2 ≤ Nat.card (G.neighborSet v)) :
    isolatedCount G = 0 := by
  have : IsEmpty {v : V // ∀ w, ¬ G.Adj v w} := by
    constructor
    rintro ⟨v, hv⟩
    have hpos : 0 < Nat.card (G.neighborSet v) := lt_of_lt_of_le (by norm_num) (hdeg v)
    obtain ⟨w, hw⟩ := (Nat.card_pos_iff.mp hpos).1
    exact hv w hw
  simp [isolatedCount]

/-- For a planar graph with no isolated vertices, Euler's inequality `#V - #E + #F ≥ 2` holds
for some rotation system. -/
