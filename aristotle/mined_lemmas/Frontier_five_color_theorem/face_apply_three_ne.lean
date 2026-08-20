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

theorem face_apply_three_ne (R : RotationSystem G) (htf : G.CliqueFree 3) (d : G.Dart) :
    (R.rot * symmPerm G) ((R.rot * symmPerm G) ((R.rot * symmPerm G) d)) ≠ d := by
  intro h
  set f := R.rot * symmPerm G with hf
  have hfst : ∀ e : G.Dart, (f e).toProd.1 = e.toProd.2 := by
    intro e
    rw [hf]
    show (R.rot (e.symm)).toProd.1 = _
    rw [R.rot_fst]
    rfl
  have h1 : G.Adj d.toProd.1 d.toProd.2 := d.adj
  have h2 : G.Adj d.toProd.2 (f d).toProd.2 := by
    have := (f d).adj
    rwa [hfst d] at this
  have h3 : G.Adj (f d).toProd.2 d.toProd.1 := by
    have hadj := (f (f d)).adj
    rw [hfst (f d)] at hadj
    have hlast : (f (f d)).toProd.2 = d.toProd.1 := by
      have := hfst (f (f d))
      rw [h] at this
      exact this.symm
    rwa [hlast] at hadj
  exact not_cliqueFree_three _ _ _ h1 h2 h3 htf

/-- Twice the number of edges is the number of darts. -/
