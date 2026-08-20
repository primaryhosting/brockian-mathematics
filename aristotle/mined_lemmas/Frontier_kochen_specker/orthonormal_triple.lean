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

lemma orthonormal_triple {u v w : E3} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (huv : ⟪u, v⟫ = 0) (huw : ⟪u, w⟫ = 0) (hvw : ⟪v, w⟫ = 0) :
    Orthonormal ℝ ![nrm u, nrm v, nrm w] := by
  constructor
  · intro i; fin_cases i <;> simp [norm_nrm, hu, hv, hw]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;>
      first
        | exact inner_nrm _ _ huv
        | exact inner_nrm _ _ huw
        | exact inner_nrm _ _ hvw
        | (rw [real_inner_comm]
           first
             | exact inner_nrm _ _ huv
             | exact inner_nrm _ _ huw
             | exact inner_nrm _ _ hvw)

variable {f : E3 → Bool}

/-- A frame function is `true` on at least one member of an orthogonal triple. -/
