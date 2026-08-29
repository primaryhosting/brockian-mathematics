import Mathlib

/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Basic definitions -/

/-- The squared Frobenius norm of a matrix, `‖M‖_F² = Re tr (Mᴴ M)`. -/

theorem two_mul_sub_one_le_sq (m : ℝ) : 2 * m - 1 ≤ m ^ 2 := by
  have hQ : ((!![m] : Matrix (Fin 1) (Fin 1) ℝ)).IsHermitian := by
    unfold Matrix.IsHermitian
    ext i j
    fin_cases i
    fin_cases j
    simp
  have hb : posIndex hQ ≤ 1 := by
    have h := Nat.card_le_card_of_injective
      (Subtype.val : {i // 0 < hQ.eigenvalues i} → Fin 1) Subtype.val_injective
    simpa [posIndex] using h
  have h := rank_trace_ineq (P := (0 : Matrix (Fin 1) (Fin 1) ℝ)) (Q := !![m])
    Matrix.PosSemidef.zero hQ 0 1 (by simp) hb 1 one_pos
  have hf : frobSq ((0 : Matrix (Fin 1) (Fin 1) ℝ) + !![m]) = m ^ 2 := by
    rw [zero_add, frobSq, Matrix.trace_fin_one]
    simp [Matrix.mul_apply]
    ring
  rw [hf] at h
  simpa using h

end Zeta23Core

