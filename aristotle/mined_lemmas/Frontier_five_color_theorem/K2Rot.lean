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

def K2Rot : RotationSystem (⊤ : SimpleGraph (Fin 2)) where
  rot := 1
  rot_fst := fun _ => rfl
  rot_transitive := by
    intro d d' hdd
    refine ⟨0, ?_⟩
    simp only [zpow_zero, Equiv.Perm.coe_one, id_eq]
    apply SimpleGraph.Dart.ext
    have hd : d.toProd = (0, 1) ∨ d.toProd = (1, 0) := by
      obtain ⟨⟨x, y⟩, h⟩ := d
      have hne : x ≠ y := h
      fin_cases x <;> fin_cases y <;> simp_all
    have hd' : d'.toProd = (0, 1) ∨ d'.toProd = (1, 0) := by
      obtain ⟨⟨x, y⟩, h⟩ := d'
      have hne : x ≠ y := h
      fin_cases x <;> fin_cases y <;> simp_all
    have hfst : d.toProd.1 = d'.toProd.1 := hdd
    rcases hd with h1 | h1 <;> rcases hd' with h2 | h2 <;> rw [h1, h2] <;> rw [h1, h2] at hfst <;>
      simp_all

/-- Non-vacuity check: the graph with a single edge is planar, with one face. -/
