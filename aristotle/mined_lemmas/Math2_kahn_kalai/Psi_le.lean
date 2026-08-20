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

theorem Psi_le {q r : ℝ} (hq : 0 < q) (hr : 64 * q ≤ r) (hr1 : r ≤ 1) (b : ℕ) :
    ∀ H : Finset (Finset α), (∀ S ∈ H, S.card ≤ b) →
      Psi r q H b ≤ ∑ m ∈ Finset.range b, (4 * q / r) ^ (m + 1) := by
  have hr0 : 0 < r := lt_of_lt_of_le (by linarith) hr
  have hy0 : 0 ≤ 4 * q / r := by positivity
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    match b with
    | 0 => intro H hH; rw [Psi_zero]; simp
    | (n + 1) =>
      intro H hH
      set b' := (n + 1) / 2 with hb'
      have hb'lt : b' < n + 1 := by omega
      rw [Psi_succ]
      have hsplit : ∑ W : Finset α, nu r W *
            (cost q (Ucov H b' W) + Psi r q (Hnext H b' W) b')
          = (∑ W : Finset α, nu r W * cost q (Ucov H b' W))
            + ∑ W : Finset α, nu r W * Psi r q (Hnext H b' W) b' := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun W _ => by ring
      have hfirst : ∑ W : Finset α, nu r W * cost q (Ucov H b' W)
          ≤ (4 * q / r) ^ (b' + 1) := by
        refine le_trans (expected_cost_le hH hq.le hr0 hr1 b') ?_
        exact geom_step_bound hq hr hr1 n
      have hsecond : ∑ W : Finset α, nu r W * Psi r q (Hnext H b' W) b'
          ≤ ∑ m ∈ Finset.range b', (4 * q / r) ^ (m + 1) := by
        calc ∑ W : Finset α, nu r W * Psi r q (Hnext H b' W) b'
            ≤ ∑ W : Finset α, nu r W * ∑ m ∈ Finset.range b', (4 * q / r) ^ (m + 1) := by
              refine Finset.sum_le_sum fun W _ => ?_
              exact mul_le_mul_of_nonneg_left
                (ih b' hb'lt (Hnext H b' W) (Hnext_bounded H b' W))
                (nu_nonneg hr0.le hr1 W)
          _ = ∑ m ∈ Finset.range b', (4 * q / r) ^ (m + 1) := by
              rw [← Finset.sum_mul, sum_nu, one_mul]
      have hcomb : ∑ m ∈ Finset.range b', (4 * q / r) ^ (m + 1) + (4 * q / r) ^ (b' + 1)
          = ∑ m ∈ Finset.range (b' + 1), (4 * q / r) ^ (m + 1) := by
        rw [Finset.sum_range_succ]
      have hmono : ∑ m ∈ Finset.range (b' + 1), (4 * q / r) ^ (m + 1)
          ≤ ∑ m ∈ Finset.range (n + 1), (4 * q / r) ^ (m + 1) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun m _ _ => by positivity)
        intro m hm
        simp only [Finset.mem_range] at hm ⊢
        omega
      rw [hsplit]
      linarith

/-- The total bound: `Psi` is at most `8 * q / r`. -/
