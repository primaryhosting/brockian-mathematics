import Mathlib
/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical
open scoped ComplexOrder

set_option maxHeartbeats 1000000

namespace Frontier

open Matrix

variable {n : ℕ}

/-! ## Basic notions -/

/-- The rank-one (orthogonal) projection onto the line spanned by a unit vector `v`,
written as the matrix `v vᴴ`. -/

lemma proj2_offdiag_ne_zero {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : IsProj P)
    (h : (P 0 0).re = 1 / 2) : P 0 1 ≠ 0 := by
  have hherm : (starRingEnd ℂ) (P 0 0) = P 0 0 := by
    have h' := congrFun (congrFun hP.1 0) 0
    simpa [Matrix.conjTranspose_apply] using h'
  have hP00 : P 0 0 = (1 / 2 : ℂ) := by
    have him : (P 0 0).im = 0 := by
      have h' := congrArg Complex.im hherm
      simp only [Complex.conj_im] at h'
      linarith
    exact Complex.ext (by simpa using h) (by simpa using him)
  have h10 : P 1 0 = (starRingEnd ℂ) (P 0 1) := by
    have h' := congrFun (congrFun hP.1 1) 0
    simpa [Matrix.conjTranspose_apply] using h'.symm
  have hmul := congrFun (congrFun hP.2 0) 0
  rw [Matrix.mul_apply, Fin.sum_univ_two] at hmul
  rw [hP00, h10] at hmul
  intro hz
  rw [hz] at hmul
  simp at hmul

