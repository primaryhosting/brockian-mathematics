import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede any module docstring, so the header block
-- above appears immediately after the single `import Mathlib` line.)

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial Matrix

/-- The adjacency matrix of the cycle graph `C₅` written out explicitly. -/

lemma exists_eigenvector_of_isRoot_charpoly {A : Matrix (Fin 5) (Fin 5) ℝ} {m : ℝ}
    (h : A.charpoly.eval m = 0) : ∃ v : Fin 5 → ℝ, v ≠ 0 ∧ A *ᵥ v = m • v := by
  rw [Matrix.eval_charpoly] at h
  have hdet : (A - (Matrix.scalar (Fin 5)) m).det = 0 := by
    have hn : A - (Matrix.scalar (Fin 5)) m = -((Matrix.scalar (Fin 5)) m - A) := by
      rw [neg_sub]
    rw [hn, Matrix.det_neg, h]
    simp
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, sub_eq_zero] at hv0
  rw [hv0]
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

/-- Each of the five numbers `2 cos (2πk/5)` really is an eigenvalue of the adjacency matrix of
`C₅`: there is a nonzero vector `v` with `A *ᵥ v = 2 cos (2πk/5) • v`. -/
