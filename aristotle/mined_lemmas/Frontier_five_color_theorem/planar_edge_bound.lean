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

theorem planar_edge_bound [Nonempty V] (hp : IsPlanar G)
    (hdeg : ∀ v : V, 2 ≤ Nat.card (G.neighborSet v)) :
    (Nat.card G.edgeSet : ℤ) ≤ 3 * (Fintype.card V : ℤ) - 6 := by
  obtain ⟨R, hE⟩ := exists_rotationSystem_euler hp hdeg
  have hfix := R.rot_apply_ne hdeg
  have h3 : 3 * R.faceCount ≤ Nat.card G.Dart :=
    three_mul_numOrbits_le _ (face_apply_ne R) (face_apply_apply_ne R hfix)
  rw [card_dart_eq] at h3
  have h3' : (3 : ℤ) * (R.faceCount : ℤ) ≤ 2 * (Nat.card G.edgeSet : ℤ) := by exact_mod_cast h3
  linarith

/-- **Euler's edge bound for triangle-free graphs**: a triangle-free planar simple graph in which
every vertex has at least two neighbours has at most `2 #V - 4` edges. -/
