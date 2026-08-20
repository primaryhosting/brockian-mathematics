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

lemma inner_emb_basis {n : ℕ} (hn : 3 ≤ n) {b : Fin n → E} (hb : Orthonormal ℝ b) (x : E3)
    {m : Fin n} (hm : 3 ≤ (m : ℕ)) : ⟪emb hn b x, b m⟫ = 0 := by
  rw [emb, sum_inner]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [real_inner_smul_left, hb.2 (by simp [Fin.ext_iff]; omega), mul_zero]

/-- If a valuation `f` is `true` at exactly one member of every orthonormal basis, and if
`b` is an orthonormal basis all of whose members except `b z` are given the value `false`,
then restricting `f` to the three-dimensional subspace spanned by `b 0, b 1, b 2`
(which contains `b z`) yields a three-dimensional frame function, which is impossible. -/
