import Mathlib

/-!
# Pos Index Conj Le
Category: Brockian Corpus
Target: Zeta23Core.posIndex_conj_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [DecidableEq m] [Fintype d]
  [DecidableEq d]

/-- Unfolding lemma for `Matrix.toEuclideanLin`. -/

lemma posIndex_one : posIndex (1 : Matrix m m 𝕜) = Fintype.card m := by
  have hone : (1 : Matrix m m 𝕜).IsHermitian := Matrix.isHermitian_one
  have hqf : ∀ x : EuclideanSpace 𝕜 m, qform (1 : Matrix m m 𝕜) x = ‖x‖ ^ 2 := by
    intro x
    rw [qform, toEuclideanLin_apply', Matrix.one_mulVec, WithLp.toLp_ofLp,
      inner_self_eq_norm_sq_to_K]
    simp
  have hle : posIndex (1 : Matrix m m 𝕜) ≤ Fintype.card m := by
    rw [posIndex_eq_card hone, posSet]
    simpa using Finset.card_filter_le (Finset.univ : Finset m) _
  have hge : Fintype.card m ≤ posIndex (1 : Matrix m m 𝕜) := by
    have hpos : PosDefOn (1 : Matrix m m 𝕜) ⊤ := by
      intro x _ hx0
      rw [hqf x]
      have : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      positivity
    have := finrank_le_posIndex hone ⊤ hpos
    rwa [finrank_top, finrank_euclideanSpace] at this
  omega

end Zeta23Core

