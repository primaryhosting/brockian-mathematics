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

theorem exists_rotationSystem_euler [Nonempty V] (hp : IsPlanar G)
    (hdeg : ∀ v : V, 2 ≤ Nat.card (G.neighborSet v)) :
    ∃ R : RotationSystem G,
      2 ≤ (Fintype.card V : ℤ) - (Nat.card G.edgeSet : ℤ) + (R.faceCount : ℤ) := by
  obtain ⟨R, hE⟩ := hp
  refine ⟨R, ?_⟩
  have hc : 1 ≤ Nat.card G.ConnectedComponent := by
    have : Nonempty G.ConnectedComponent := ⟨G.connectedComponentMk (Classical.arbitrary V)⟩
    exact Nat.card_pos
  have hc' : (1 : ℤ) ≤ (Nat.card G.ConnectedComponent : ℤ) := by exact_mod_cast hc
  rw [isolatedCount_eq_zero hdeg] at hE
  push_cast at hE
  linarith

/-- **Euler's edge bound**: a planar simple graph in which every vertex has at least two
neighbours has at most `3 #V - 6` edges. -/
