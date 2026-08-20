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

theorem face_apply_apply_ne (R : RotationSystem G) (hfix : ∀ d : G.Dart, R.rot d ≠ d)
    (d : G.Dart) : (R.rot * symmPerm G) ((R.rot * symmPerm G) d) ≠ d := by
  intro h
  have h2 : R.rot ((R.rot (d.symm)).symm) = d := h
  have hfst : (R.rot (d.symm)).toProd.1 = d.toProd.2 := by rw [R.rot_fst]; rfl
  have hsnd : (R.rot (d.symm)).toProd.2 = d.toProd.1 := by
    have h3 : (R.rot ((R.rot (d.symm)).symm)).toProd.1 = d.toProd.1 := by rw [h2]
    rwa [R.rot_fst] at h3
  have key : R.rot (d.symm) = d.symm := by
    apply SimpleGraph.Dart.ext
    rw [SimpleGraph.Dart.symm_toProd]
    exact Prod.ext hfst hsnd
  exact hfix d.symm key

omit [Fintype V] in
/-- Three mutually adjacent vertices form a triangle. -/
