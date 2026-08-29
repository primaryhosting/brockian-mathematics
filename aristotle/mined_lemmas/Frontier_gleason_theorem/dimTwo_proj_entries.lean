import RequestProject.Main
/-!
# Gleason's theorem fails in dimension two

This file complements `RequestProject/Main.lean`.  It constructs an explicit quantum measure on
the projection lattice of `ℂ²` which does not come from any density operator, showing that the
dimension hypothesis `3 ≤ N` in Gleason's theorem cannot be dropped.

The measure is the two-valued "lexicographic sign" measure: in dimension two the only nontrivial
orthogonality relation between projections is `Q = 1 - P` for a rank-one projection `P`, so any
function on rank-one projections satisfying `f P + f (1 - P) = 1` is finitely additive.
-/

open scoped Classical
open scoped ComplexOrder

namespace Frontier

open Matrix

/-! ## Structure of projections in dimension two -/

/-- The Cayley–Hamilton identity for `2 × 2` matrices. -/

lemma dimTwo_proj_entries {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : IsProj P) :
    (P 0 0).im = 0 ∧ (P 0 0).re ^ 2 + Complex.normSq (P 0 1) = (P 0 0).re := by
  have hh : P 1 0 = star (P 0 1) := by
    have h := hP.1.apply 0 1
    rw [← h, star_star]
  have h00 : star (P 0 0) = P 0 0 := hP.1.apply 0 0
  have him : (P 0 0).im = 0 := Complex.conj_eq_iff_im.mp h00
  refine ⟨him, ?_⟩
  have h := congrFun (congrFun hP.2 0) 0
  rw [Matrix.mul_apply, Fin.sum_univ_two, hh] at h
  have hre := congrArg Complex.re h
  simp [Complex.mul_re, Complex.normSq_apply, him] at hre ⊢
  nlinarith [hre]

/-! ## A two-valued quantum measure on `ℂ²` -/

/-- Lexicographic positivity of a triple of reals with respect to the "origin" `(1/2, 0, 0)`. -/
