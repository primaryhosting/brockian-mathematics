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

private lemma reduction {n : ℕ} (hn : 3 ≤ n) (f : EuclideanSpace ℝ (Fin n) → Bool)
    (H : ∀ v : Fin n → EuclideanSpace ℝ (Fin n), Orthonormal ℝ v → ∃! i, f (v i) = true)
    {b : Fin n → EuclideanSpace ℝ (Fin n)} (hb : Orthonormal ℝ b)
    {z : Fin n} (hzval : (z : ℕ) = 0)
    (hbfalse : ∀ m : Fin n, m ≠ z → f (b m) = false) : False := by
  refine no_frame_function_three (fun x => f (emb hn b x)) ?_
  intro v hv
  set w : Fin n → EuclideanSpace ℝ (Fin n) :=
    fun m => if h : (m : ℕ) < 3 then emb hn b (v ⟨m, h⟩) else b m with hw
  have hvite := orthonormal_iff_ite.1 hv
  have hbite := orthonormal_iff_ite.1 hb
  have hwo : Orthonormal ℝ w := by
    rw [orthonormal_iff_ite]
    intro i j
    by_cases hi : (i : ℕ) < 3 <;> by_cases hj : (j : ℕ) < 3 <;>
      simp only [hw, dif_pos, hi, hj, dite_false]
    · rw [inner_emb hn hb, hvite]
      congr 1
      simp [Fin.ext_iff]
    · rw [inner_emb_basis hn hb _ (by omega), if_neg (by rintro rfl; omega)]
    · rw [real_inner_comm, inner_emb_basis hn hb _ (by omega), if_neg (by rintro rfl; omega)]
    · exact hbite i j
  obtain ⟨M, hM, hMu⟩ := H w hwo
  have hM3 : (M : ℕ) < 3 := by
    by_contra hc
    have hwM : w M = b M := dif_neg hc
    rw [hwM, hbfalse M (by rintro rfl; omega)] at hM
    exact absurd hM (by simp)
  refine ⟨⟨M, hM3⟩, ?_, ?_⟩
  · have hwM : w M = emb hn b (v ⟨M, hM3⟩) := dif_pos hM3
    rw [hwM] at hM
    exact hM
  · intro j hj
    have hcast : w (Fin.castLE hn j) = emb hn b (v j) := by
      simp only [hw]
      rw [dif_pos (show ((Fin.castLE hn j : Fin n) : ℕ) < 3 by simp)]
      rfl
    have hjM := hMu (Fin.castLE hn j) (show f (w (Fin.castLE hn j)) = true by rw [hcast]; exact hj)
    exact Fin.ext (by simpa [Fin.ext_iff] using hjM)

/-- **The Kochen–Specker theorem.**  In dimension `n ≥ 3` there is no noncontextual
hidden-variable assignment: there is no map `f` assigning a truth value to each vector of
`ℝⁿ` such that every orthonormal basis contains exactly one vector with value `true`.

(Such an `f` is what a noncontextual assignment of definite outcomes to the rank-one
projections would provide: for a complete family of orthogonal rank-one projections
exactly one outcome must occur, independently of which basis the projection is measured in.) -/
