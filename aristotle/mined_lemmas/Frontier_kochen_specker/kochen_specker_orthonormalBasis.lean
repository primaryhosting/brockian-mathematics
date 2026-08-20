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

theorem kochen_specker_orthonormalBasis (n : ℕ) (hn : 3 ≤ n)
    (f : EuclideanSpace ℝ (Fin n) → Bool) :
    ¬ ∀ B : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)), ∃! i, f (B i) = true := by
  intro H
  refine kochen_specker n hn f ?_
  intro v hv
  have hne : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by simp
  let Bv := basisOfOrthonormalOfCardEqFinrank hv hcard
  have hcoe : ⇑Bv = v := coe_basisOfOrthonormalOfCardEqFinrank hv hcard
  let OB := Bv.toOrthonormalBasis (by rw [hcoe]; exact hv)
  have hOB : ∀ i, OB i = v i := by
    intro i
    show (OB : Fin n → _) i = v i
    rw [Module.Basis.coe_toOrthonormalBasis, hcoe]
  obtain ⟨i, hi, hu⟩ := H OB
  exact ⟨i, by simp only [hOB] at hi; exact hi, fun j hj => hu j (by simp only [hOB]; exact hj)⟩

end Frontier

