import Mathlib

/-!
# Kochen–Specker: the three-dimensional core

This file contains the combinatorial/geometric heart of the Kochen–Specker theorem:
there is no `{0,1}`-valued "frame function" on `ℝ³`, i.e. no map assigning to every
unit vector a truth value in such a way that every orthonormal basis contains
exactly one vector with value `true`.

The proof uses the 33 rays of Peres, whose coordinates lie in `{0, ±1, ±√2}`.
Each constraint is certified by an explicit orthogonal triple of vectors, and the
resulting propositional constraint system is refuted by an explicit case analysis.
-/

namespace KochenSpecker

open scoped RealInnerProductSpace

/-- Three-dimensional real Euclidean space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- A vector of `ℝ³` given by its three coordinates. -/

theorem pair_right (h : ¬(A ∧ B)) (hb : B) : ¬A := fun ha => h ⟨ha, hb⟩

end Propositional

/-- **Kochen–Specker, dimension three.**  There is no `{0,1}`-valued frame function on
three-dimensional Euclidean space: no assignment of truth values to unit vectors such
that every orthonormal basis carries exactly one `true` value. -/
