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

theorem kochen_specker (n : ℕ) (hn : 3 ≤ n) (f : EuclideanSpace ℝ (Fin n) → Bool) :
    ¬ ∀ v : Fin n → EuclideanSpace ℝ (Fin n), Orthonormal ℝ v → ∃! i, f (v i) = true := by
  intro H
  set B : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    EuclideanSpace.basisFun (Fin n) ℝ
  have hb0 : Orthonormal ℝ (fun i => B i) := B.orthonormal
  obtain ⟨i₀, hi₀, huniq₀⟩ := H _ hb0
  set z : Fin n := ⟨0, by omega⟩ with hz
  set σ : Equiv.Perm (Fin n) := Equiv.swap z i₀ with hσ
  set b : Fin n → EuclideanSpace ℝ (Fin n) := fun m => B (σ m) with hbdef
  have hb : Orthonormal ℝ b := hb0.comp σ σ.injective
  have hbfalse : ∀ m : Fin n, m ≠ z → f (b m) = false := by
    intro m hm
    by_contra hcon
    have htrue : f (b m) = true := by simpa using hcon
    have hσm := huniq₀ (σ m) (by simpa [hbdef] using htrue)
    exact hm (σ.injective (by simpa [hσ] using hσm))
  exact reduction hn f H hb (by simp [hz]) hbfalse

/-- **The Kochen–Specker theorem**, stated for orthonormal bases: in dimension `n ≥ 3`
no truth-value assignment makes exactly one member of each orthonormal basis `true`. -/
