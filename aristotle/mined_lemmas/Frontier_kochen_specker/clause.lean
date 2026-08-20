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

theorem clause (H : ∀ v : Fin 3 → E3, Orthonormal ℝ v → ∃! i, f (v i) = true)
    {u v w : E3} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (huv : ⟪u, v⟫ = 0) (huw : ⟪u, w⟫ = 0) (hvw : ⟪v, w⟫ = 0) :
    f (nrm u) = true ∨ f (nrm v) = true ∨ f (nrm w) = true := by
  obtain ⟨i, hi, -⟩ := H _ (orthonormal_triple hu hv hw huv huw hvw)
  fin_cases i
  · exact Or.inl (by simpa using hi)
  · exact Or.inr (Or.inl (by simpa using hi))
  · exact Or.inr (Or.inr (by simpa using hi))

/-- A frame function cannot be `true` on two orthogonal vectors. -/
