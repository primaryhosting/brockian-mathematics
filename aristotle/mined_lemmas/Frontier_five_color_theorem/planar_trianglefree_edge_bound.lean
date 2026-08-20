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

theorem planar_trianglefree_edge_bound [Nonempty V] (hp : IsPlanar G) (htf : G.CliqueFree 3)
    (hdeg : ∀ v : V, 2 ≤ Nat.card (G.neighborSet v)) :
    (Nat.card G.edgeSet : ℤ) ≤ 2 * (Fintype.card V : ℤ) - 4 := by
  obtain ⟨R, hE⟩ := exists_rotationSystem_euler hp hdeg
  have hfix := R.rot_apply_ne hdeg
  have h4 : 4 * R.faceCount ≤ Nat.card G.Dart :=
    four_mul_numOrbits_le _ (face_apply_ne R) (face_apply_apply_ne R hfix)
      (face_apply_three_ne R htf)
  rw [card_dart_eq] at h4
  have h4' : (4 : ℤ) * (R.faceCount : ℤ) ≤ 2 * (Nat.card G.edgeSet : ℤ) := by exact_mod_cast h4
  linarith

/-- The handshake inequality: if every vertex has degree at least `m` then `m #V ≤ 2 #E`. -/
