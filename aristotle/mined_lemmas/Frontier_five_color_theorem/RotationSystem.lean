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

theorem RotationSystem.rot_apply_ne (R : RotationSystem G)
    (hdeg : ∀ v : V, 2 ≤ Nat.card (G.neighborSet v)) (d : G.Dart) : R.rot d ≠ d := by
  intro hd
  have hnt : Nontrivial (G.neighborSet d.toProd.1) :=
    Finite.one_lt_card_iff_nontrivial.mp (hdeg _)
  obtain ⟨x, hx⟩ := exists_ne (⟨d.toProd.2, d.adj⟩ : G.neighborSet d.toProd.1)
  set d' : G.Dart := ⟨(d.toProd.1, x.1), x.2⟩ with hd'
  obtain ⟨k, hk⟩ := R.rot_transitive d d' rfl
  rw [Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hd k] at hk
  apply hx
  apply Subtype.ext
  have := congrArg (fun y : G.Dart => y.toProd.2) hk
  simpa [hd'] using this.symm

omit [Fintype V] in
/-- No face of an embedding of a simple graph has a single side: this would be a loop. -/
