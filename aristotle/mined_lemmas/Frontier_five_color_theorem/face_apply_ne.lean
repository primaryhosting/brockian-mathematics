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

theorem face_apply_ne (R : RotationSystem G) (d : G.Dart) :
    (R.rot * symmPerm G) d ≠ d := by
  intro h
  have h1 : (R.rot (d.symm)).fst = d.fst := by
    rw [show R.rot (d.symm) = (R.rot * symmPerm G) d from rfl, h]
  rw [R.rot_fst] at h1
  exact SimpleGraph.Dart.fst_ne_snd d h1.symm

omit [Fintype V] in
/-- No face of an embedding of a simple graph has exactly two sides: this would either be a
double edge or a vertex fixed by the rotation. -/
