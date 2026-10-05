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

lemma exists_range_proj {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    ∃ F B : Matrix n n 𝕜, Fᴴ = F ∧ F * F = F ∧ A * F = A ∧ A * B = F ∧
      RCLike.re F.trace = (A.rank : ℝ) := by
  classical
  refine ⟨hFun hA.1 (fun x => if x ≠ 0 then 1 else 0),
    hFun hA.1 (fun x => if x ≠ 0 then x⁻¹ else 0), hFun_isHermitian hA.1 _, ?_, ?_, ?_, ?_⟩
  · rw [hFun_mul]
    exact hFun_congr hA.1 fun i => by split_ifs <;> norm_num
  · have key : hFun hA.1 (fun x => x) * hFun hA.1 (fun x => if x ≠ 0 then (1:ℝ) else 0)
        = hFun hA.1 (fun x => x * (if x ≠ 0 then (1:ℝ) else 0)) := hFun_mul hA.1 _ _
    rw [hFun_id] at key
    rw [key, show (hFun hA.1 fun x => x * (if x ≠ 0 then (1:ℝ) else 0))
        = hFun hA.1 (fun x => x) from hFun_congr hA.1 fun i => by
          split_ifs with h
          · ring
          · simp only [ne_eq, not_not] at h; simp [h]]
    exact hFun_id hA.1
  · have key : hFun hA.1 (fun x => x) * hFun hA.1 (fun x => if x ≠ 0 then x⁻¹ else 0)
        = hFun hA.1 (fun x => x * (if x ≠ 0 then x⁻¹ else 0)) := hFun_mul hA.1 _ _
    rw [hFun_id] at key
    rw [key]
    exact hFun_congr hA.1 fun i => by
      split_ifs with h
      · exact mul_inv_cancel₀ h
      · ring
  · rw [re_trace_hFun, hA.1.rank_eq_card_non_zero_eigs, Fintype.card_subtype, Finset.card_filter]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp_all

/-! ## Two computations with the test matrix -/

