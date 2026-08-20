import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
Covers, costs, and minimum fragments (Park–Pham).
-/
import Mathlib
import RequestProject.KahnKalai.Measure

open Finset
open scoped Classical

namespace Math2

variable {α : Type*} [DecidableEq α]

/-! ## Covers and their costs -/

/-- `G` is a cover of `H`: every member of `H` contains a member of `G`. -/

theorem covCost_mul_Fail_le {q r : ℝ} (hq : 0 ≤ q) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (b : ℕ) :
    ∀ H : Finset (Finset α), (∀ S ∈ H, S.card ≤ b) →
      covCost q H * Fail (pp r b) H ≤ Psi r q H b := by
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    match b with
    | 0 =>
      intro H hH
      rw [Psi_zero]
      by_cases hemp : H = ∅
      · subst hemp
        rw [covCost_empty hq]
        simp
      · obtain ⟨S, hS⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
        have hS0 : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp (hH S hS))
        have hFail : Fail (pp r 0) H = 0 := by
          rw [Fail]
          refine Finset.sum_eq_zero fun V _ => ?_
          have : ∃ S' ∈ H, S' ⊆ V := ⟨S, hS, by rw [hS0]; exact Finset.empty_subset V⟩
          simp [this]
        rw [hFail, mul_zero]
    | (n + 1) =>
      intro H hH
      set b' := (n + 1) / 2 with hb'
      have hb'lt : b' < n + 1 := by omega
      have hs0 : 0 ≤ pp r b' := pp_nonneg hr0 hr1 b'
      have hs1 : pp r b' ≤ 1 := pp_le_one hr0 hr1 b'
      calc covCost q H * Fail (pp r (n + 1)) H
          ≤ covCost q H * ∑ W : Finset α, nu r W * Fail (pp r b') (Hnext H b' W) :=
            mul_le_mul_of_nonneg_left (Fail_step hr0 hr1 H n) (covCost_nonneg hq H)
        _ = ∑ W : Finset α, nu r W * (covCost q H * Fail (pp r b') (Hnext H b' W)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun W _ => by ring
        _ ≤ ∑ W : Finset α, nu r W * (cost q (Ucov H b' W) + Psi r q (Hnext H b' W) b') := by
            refine Finset.sum_le_sum fun W _ => ?_
            refine mul_le_mul_of_nonneg_left ?_ (nu_nonneg hr0 hr1 W)
            have hstep := covCost_le_step hq H b' W
            have hIH := ih b' hb'lt (Hnext H b' W) (Hnext_bounded H b' W)
            have hF0 := Fail_nonneg hs0 hs1 (Hnext H b' W)
            have hF1 := Fail_le_one hs0 hs1 (Hnext H b' W)
            have hc := cost_nonneg hq (Ucov H b' W)
            have e1 : covCost q H * Fail (pp r b') (Hnext H b' W)
                ≤ (cost q (Ucov H b' W) + covCost q (Hnext H b' W))
                    * Fail (pp r b') (Hnext H b' W) :=
              mul_le_mul_of_nonneg_right hstep hF0
            rw [add_mul] at e1
            have e2 : cost q (Ucov H b' W) * Fail (pp r b') (Hnext H b' W)
                ≤ cost q (Ucov H b' W) := mul_le_of_le_one_right hc hF1
            linarith
        _ = Psi r q H (n + 1) := (Psi_succ r q H n).symm

/-! ## Bounding `Psi` -/

