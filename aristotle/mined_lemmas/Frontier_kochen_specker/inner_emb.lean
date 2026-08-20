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

lemma inner_emb {n : ℕ} (hn : 3 ≤ n) {b : Fin n → E} (hb : Orthonormal ℝ b) (x y : E3) :
    ⟪emb hn b x, emb hn b y⟫ = ⟪x, y⟫ := by
  have hb' : Orthonormal ℝ (b ∘ Fin.castLE hn) := hb.comp _ (castLE_inj hn)
  have key := hb'.inner_sum (fun t => x t) (fun t => y t) Finset.univ
  simp only [Function.comp_apply] at key
  rw [emb, emb, key]
  simp [PiLp.inner_apply, mul_comm]

