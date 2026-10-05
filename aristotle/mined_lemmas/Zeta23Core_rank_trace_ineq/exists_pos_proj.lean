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

lemma exists_pos_proj {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) :
    ∃ E R S : Matrix n n 𝕜, Eᴴ = E ∧ Rᴴ = R ∧ E + R = 1 ∧ E * E = E ∧ R * R = R ∧
      E * R = 0 ∧ R * E = 0 ∧ R * Q * R = -S ∧ S.PosSemidef ∧
      RCLike.re E.trace = (posIndex hQ : ℝ) := by
  classical
  refine ⟨hFun hQ (fun x => if 0 < x then 1 else 0), hFun hQ (fun x => if 0 < x then 0 else 1),
    hFun hQ (fun x => if 0 < x then 0 else -x), hFun_isHermitian hQ _, hFun_isHermitian hQ _,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hFun_add, ← hFun_one hQ]
    exact hFun_congr hQ fun i => by split_ifs <;> norm_num
  · rw [hFun_mul]
    exact hFun_congr hQ fun i => by split_ifs <;> norm_num
  · rw [hFun_mul]
    exact hFun_congr hQ fun i => by split_ifs <;> norm_num
  · rw [hFun_mul, ← hFun_zero hQ]
    exact hFun_congr hQ fun i => by split_ifs <;> norm_num
  · rw [hFun_mul, ← hFun_zero hQ]
    exact hFun_congr hQ fun i => by split_ifs <;> norm_num
  · have key : hFun hQ (fun x => if 0 < x then (0:ℝ) else 1) * hFun hQ (fun x => x) *
        hFun hQ (fun x => if 0 < x then (0:ℝ) else 1)
        = hFun hQ (fun x => (if 0 < x then (0:ℝ) else 1) * x * (if 0 < x then (0:ℝ) else 1)) := by
      rw [hFun_mul, hFun_mul]
    rw [hFun_id] at key
    rw [key, eq_comm, neg_eq_iff_add_eq_zero, hFun_add, ← hFun_zero hQ]
    exact hFun_congr hQ fun i => by split_ifs <;> ring
  · refine hFun_posSemidef hQ fun i => ?_
    split_ifs with h
    · exact le_refl 0
    · linarith [not_lt.mp h]
  · rw [re_trace_hFun, posIndex, Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp [Finset.sum_boole]

/-- The orthogonal projection onto the range of a positive semidefinite matrix `A`. -/
